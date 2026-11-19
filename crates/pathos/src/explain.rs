//! `--explain`: where the compiled checker stops accepting a proof.
//!
//! The verdict comes from one call of `check_proof`, which says only
//! `incorrect`. To say more, this runs the generated checking loop one
//! command at a time and looks at the state in between. That is not part
//! of the interface the generator documents (it calls the functions that
//! `functions.tsv` lists for `$eo_invoke_assume_list`, `$eo_invoke_cmd`
//! and `$eo_state_is_refutation`), so it is kept apart from the adapter
//! and never decides a verdict. `--profile` does the same to say where the
//! time goes.

use pathos_compiled_checker as cc;
use pathos_compiled_checker::generated as g;
use pathos_compiled_checker::{CheckResult, Store, TermData};

/// A store term as text, down to `depth` levels.
pub fn show(s: &Store, t: cc::Term, depth: usize) -> String {
    let Ok(data) = s.view(t) else {
        return "<invalid>".into();
    };
    if depth == 0 {
        return "...".into();
    }
    match data {
        TermData::Stuck => "<stuck>".into(),
        TermData::Literal(l) | TermData::Native(l) => match l {
            cc::Lit::Str(_) => format!("\"{l}\""),
            cc::Lit::Binary(b) => format!("#b{}", b.to_string_base(2)),
            _ => l.to_string(),
        },
        TermData::UserOp(c) => c.name().to_string(),
        TermData::Apply(f, a) => {
            format!("(_ {} {})", show(s, *f, depth - 1), show(s, *a, depth - 1))
        }
        TermData::Node(c, fields) if fields.is_empty() => c.name().to_string(),
        TermData::Node(c, fields) => {
            let mut out = format!("({}", c.name());
            for &f in fields {
                out.push(' ');
                out.push_str(&show(s, f, depth - 1));
            }
            out.push(')');
            out
        }
    }
}

/// Runs the commands one by one and describes the first one that leaves
/// the state stuck, or what is wrong with the final state.
pub fn explain(
    s: &mut Store,
    assumptions: cc::Term,
    commands: &[cc::Term],
    labels: &[String],
) -> CheckResult<String> {
    let stuck = s.named("$emb_s.Stuck", &[])?;
    let nil = s.named("$emb_s.nil", &[])?;
    let mut state = g::eo__24eo_5finvoke_5fassume_5flist(s, nil, assumptions)?;
    if state == stuck {
        return Ok("an assumption is not a closed formula of type Bool".into());
    }
    for (i, &cmd) in commands.iter().enumerate() {
        let next = g::eo__24eo_5finvoke_5fcmd(s, state, cmd)?;
        if next == stuck {
            let label = labels.get(i).map_or("a command", String::as_str);
            let mut out = format!(
                "the checker does not accept {label}\n  command: {}",
                show(s, cmd, 12)
            );
            if let Some(fields) = s.destruct(
                cc::Constructor::from_name("$emb_s.cons")
                    .ok_or(cc::CheckError::InvalidConstructor)?,
                state,
            )? {
                out.push_str(&format!(
                    "\n  top of the state before it: {}",
                    show(s, fields[0], 12)
                ));
            }
            return Ok(out);
        }
        state = next;
    }
    let answer = g::eo__24eo_5fstate_5fis_5frefutation(s, state)?;
    Ok(if s.boolean_value(answer, true)? == Some(true) {
        "every command is accepted and the state is a refutation".into()
    } else {
        "every command is accepted, but the proof does not end with false proved outside \
         every assume-push"
            .into()
    })
}

/// Runs the commands one by one and returns the time each took, in
/// seconds, with what the state was after the last one run: for
/// `--profile`.
pub fn time_commands(
    s: &mut Store,
    assumptions: cc::Term,
    commands: &[cc::Term],
) -> CheckResult<Vec<f64>> {
    let stuck = s.named("$emb_s.Stuck", &[])?;
    let nil = s.named("$emb_s.nil", &[])?;
    let mut state = g::eo__24eo_5finvoke_5fassume_5flist(s, nil, assumptions)?;
    let mut times = Vec::with_capacity(commands.len());
    for &cmd in commands {
        if state == stuck {
            break;
        }
        let start = std::time::Instant::now();
        state = g::eo__24eo_5finvoke_5fcmd(s, state, cmd)?;
        times.push(start.elapsed().as_secs_f64());
    }
    Ok(times)
}
