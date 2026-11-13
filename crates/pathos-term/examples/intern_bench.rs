//! Micro-benchmark of the term store (milestone 1 in docs/brief.md).
//!
//! Interns about 4 million terms shaped like those of a proof: almost all
//! are binary applications `((f a) b)` of a few hundred function symbols to
//! earlier terms, each with a cached type. Then interns them all again, to
//! time lookups of terms that exist.
//!
//! Run with:
//!   cargo run --release -p pathos-term --example intern_bench [terms]

use std::time::Instant;

use pathos_term::{Kind, SymbolKind, Term, TermStore};

/// A small deterministic generator (xorshift64*), so runs are comparable.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 >> 12;
        self.0 ^= self.0 << 25;
        self.0 ^= self.0 >> 27;
        self.0.wrapping_mul(0x2545_F491_4F6C_DD1D)
    }

    fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }
}

struct Signature {
    /// Binary functions of type (-> S (-> S S)).
    funs: Vec<Term>,
    sort: Term,
    /// The type (-> S S) of a function applied to one argument.
    partial: Term,
}

/// When to stop requesting applications.
enum Until {
    /// The store holds this many terms.
    StoreSize(usize),
    /// This many applications were requested.
    Requests(usize),
}

/// Requests applications `((f a) b)` and caches their types. The requests
/// are the same for the same seed. Returns how many were made.
fn request_terms(store: &mut TermStore, sig: &Signature, leaves: &[Term], until: Until) -> usize {
    let mut rng = Rng(0x9E37_79B9_7F4A_7C15);
    let mut pool: Vec<Term> = leaves.to_vec();
    let mut requested = 0;
    loop {
        match until {
            Until::StoreSize(n) if store.len() >= n => break,
            Until::Requests(n) if requested >= n => break,
            _ => {}
        }
        let f = sig.funs[rng.below(sig.funs.len())];
        // Arguments are mostly recent terms, as in a proof, where a step
        // builds on the steps just before it; this also makes terms deep.
        let pick = |rng: &mut Rng, pool: &[Term]| {
            if rng.below(4) == 0 {
                pool[rng.below(pool.len())]
            } else {
                let window = pool.len().min(1000);
                pool[pool.len() - 1 - rng.below(window)]
            }
        };
        let a = pick(&mut rng, &pool);
        let b = pick(&mut rng, &pool);
        let fa = store.mk_apply(f, a);
        if store.ty(fa).is_none() {
            store.set_ty(fa, sig.partial);
        }
        let fab = store.mk_apply(fa, b);
        if store.ty(fab).is_none() {
            store.set_ty(fab, sig.sort);
        }
        requested += 2;
        pool.push(fab);
    }
    requested
}

/// The peak resident set size of this process, in bytes (Linux).
fn peak_rss_bytes() -> Option<u64> {
    let status = std::fs::read_to_string("/proc/self/status").ok()?;
    let line = status.lines().find(|l| l.starts_with("VmHWM:"))?;
    let kb: u64 = line.split_whitespace().nth(1)?.parse().ok()?;
    Some(kb * 1024)
}

fn main() {
    let target: usize = std::env::args()
        .nth(1)
        .and_then(|a| a.parse().ok())
        .unwrap_or(4_000_000);
    let mut store = TermStore::new();
    let ty = store.mk_type();
    let sort = store.mk_symbol(SymbolKind::Const, "S", ty);
    let partial = store.mk(Kind::FUNCTION_TYPE, &[sort, sort]);
    let fun_type = store.mk(Kind::FUNCTION_TYPE, &[sort, partial]);
    let funs: Vec<Term> = (0..200)
        .map(|i| store.mk_symbol(SymbolKind::Const, &format!("f{i}"), fun_type))
        .collect();
    let leaves: Vec<Term> = (0..2000)
        .map(|i| store.mk_symbol(SymbolKind::Const, &format!("c{i}"), sort))
        .collect();
    let sig = Signature {
        funs,
        sort,
        partial,
    };

    let before = store.len();
    let start = Instant::now();
    let requested = request_terms(&mut store, &sig, &leaves, Until::StoreSize(target));
    let build_time = start.elapsed();
    let terms = store.len();

    // The same requests again: every one finds an existing term.
    let start = Instant::now();
    let again = request_terms(&mut store, &sig, &leaves, Until::Requests(requested));
    let lookup_time = start.elapsed();
    assert_eq!(
        store.len(),
        terms,
        "interning the same terms again made new ones"
    );

    let ns = |d: std::time::Duration, n: usize| d.as_nanos() as f64 / n as f64;
    println!("terms in the store:      {terms}");
    println!(
        "applications requested:  {requested} ({} new terms)",
        terms - before
    );
    println!(
        "build:                   {:.3} s ({:.1} ns per request)",
        build_time.as_secs_f64(),
        ns(build_time, requested)
    );
    println!(
        "intern again (all hits): {:.3} s ({:.1} ns per request)",
        lookup_time.as_secs_f64(),
        ns(lookup_time, again)
    );
    let heap = store.heap_bytes();
    println!(
        "store tables:            {:.1} MiB ({:.1} bytes per term)",
        heap as f64 / (1024.0 * 1024.0),
        heap as f64 / terms as f64
    );
    match peak_rss_bytes() {
        Some(rss) => println!(
            "peak memory (VmHWM):     {:.1} MiB ({:.1} bytes per term)",
            rss as f64 / (1024.0 * 1024.0),
            rss as f64 / terms as f64
        ),
        None => println!("peak memory (VmHWM):     not available on this system"),
    }
}
