module
public import Init

/-!
# Eunoia's natives

Written by scripts/natives-layer from Ethos's plugins/lean_meta/lean.eos (the
`:lean-impl` of each native), the definitions lean-meta prints into every
calculus's Lean: here once, in namespace `Eunoia`, for the runtime's specs to
be stated against whatever the calculus (Eunoia/Bridge.lean relates them to
a calculus's own). Do not edit.

Left out, as they name a type of the SMT-LIB embedding that each calculus
declares (or use one that does): nat_zero, nat_succ, re_elem_valid, re_str_valid, re_nullable, re_concat, re_union, re_inter, re_comp, re_mult, re_deriv, re_prefix_match_len?, re_positive_prefix_match_len?, re_find_idx_from, str_to_re, re_diff, re_range, str_in_re, str_indexof_re, str_indexof_re_split, str_replace_re, str_replace_re_all, str_occur_index_re, re_allchar, re_none, re_all, re_ext_eq, eval_map_diff, eval_seq_diff, eval_exists, eval_forall, eval_choice, eval_bind, unpack_seq, pack_seq, unpack_string, pack_string, seq_len, seq_concat, seq_extract, seq_indexof, seq_contains, seq_replace, seq_replace_all, seq_occur_index, seq_update, seq_rev.
-/

set_option linter.unusedVariables false

@[expose] public section

namespace Eunoia

abbrev native_Bool := Bool

abbrev native_Int := Int

abbrev native_Rat := Rat

abbrev native_Nat := Nat

abbrev native_Char := Nat

abbrev native_String := List native_Char

def native_z_max_code_point : native_Int := 196607

def native_char_valid (c : native_Char) : native_Bool :=
  decide ((c : native_Int) <= native_z_max_code_point)

def native_string_valid (s : native_String) : native_Bool :=
  s.all native_char_valid

def native_string_lit (s : String) : native_String :=
  s.toList.map Char.toNat

def native_string_prefix_eq : native_String -> native_String -> native_Bool
  | [], _ => true
  | _ :: _, [] => false
  | c :: cs, d :: ds => decide (c = d) && native_string_prefix_eq cs ds

def native_ite {T : Type} (c : native_Bool) (t e : T) : T :=
  if c then t else e

def native_not : native_Bool -> native_Bool
  | x => Bool.not x

def native_and : native_Bool -> native_Bool -> native_Bool
  | x, y => x && y

def native_iff : native_Bool -> native_Bool -> native_Bool
  | x, y => decide (x = y)

def native_or : native_Bool -> native_Bool -> native_Bool
  | x, y => x || y

def native_zplus : native_Int -> native_Int -> native_Int
  | x, y => x+y

def native_zmult : native_Int -> native_Int -> native_Int
  | x, y => x*y

def native_zneg : native_Int -> native_Int
  | x => -x

def native_zeq : native_Int -> native_Int -> native_Bool
  | x, y => decide (x = y)

def native_zleq : native_Int -> native_Int -> native_Bool
  | x, y => decide (x <= y)

def native_zlt : native_Int -> native_Int -> native_Bool
  | x, y => decide (x < y)

def native_div_total : native_Int -> native_Int -> native_Int
  | x, y => x/y

def native_mod_total : native_Int -> native_Int -> native_Int
  | x, y => x%y

def native_zexp_total (x : native_Int) (y : native_Int) : native_Int :=
  if y < 0 then 0 else (x ^ (Int.toNat y))

-- Helper for native_int_log: repeatedly divides `remaining` by `base`, counting
-- the steps until it drops below `base`. `fuel` bounds the recursion (the caller
-- passes the value itself, which is always at least the number of steps when
-- base >= 2).
def impl_native_int_log_rec (base : native_Nat) : native_Nat -> native_Nat -> native_Nat
  | 0, _ => 0
  | fuel + 1, remaining =>
    if remaining < base then 0 else 1 + impl_native_int_log_rec base fuel (remaining / base)

-- The (rounded-down) integer logarithm of `v` in base `b`, i.e. the greatest
-- m >= 0 such that b^m <= v, or 0 when b <= 1 or v <= 0. This aligns with Lean's
-- `Nat.log` and is the integer inverse of native_zexp_total.
def native_int_log (b : native_Int) (v : native_Int) : native_Int :=
  let base := Int.toNat b
  let value := Int.toNat v
  if base <= 1 || value == 0 then 0 else Int.ofNat (impl_native_int_log_rec base value value)

def native_int_pow2 (n : native_Int) : native_Int :=
  (native_zexp_total 2 n)

def native_piand : native_Int -> native_Int -> native_Int -> native_Int
  | w, x, y => ((BitVec.ofInt (Int.toNat w) x) &&& (BitVec.ofInt (Int.toNat w) y)).toInt

def native_mk_rational : native_Int -> native_Int -> native_Rat
  | x, y => x/y

def native_qplus : native_Rat -> native_Rat -> native_Rat
  | x, y => x+y

def native_qmult : native_Rat -> native_Rat -> native_Rat
  | x, y => x*y

def native_qneg : native_Rat -> native_Rat
  | x => -x

def native_qeq : native_Rat -> native_Rat -> native_Bool
  | x, y => decide (x = y)

def native_qleq : native_Rat -> native_Rat -> native_Bool
  | x, y => decide (x <= y)

def native_qlt : native_Rat -> native_Rat -> native_Bool
  | x, y => decide (x < y)

def native_qdiv_total : native_Rat -> native_Rat -> native_Rat
  | x, y => x/y

def native_qexp_total (x : native_Rat) (y : native_Int) : native_Rat :=
  if y < 0 then (native_mk_rational 0 1) else (x ^ (Int.toNat y))

def native_to_int : native_Rat -> native_Int
  | x => (Rat.floor x)

def native_to_real : native_Int -> native_Rat
  | x => (native_mk_rational x 1)

def native_str_to_code (s : native_String) : native_Int :=
  match s with
  | [c] => if native_char_valid c then Int.ofNat c else -1
  | _   => -1

def native_str_from_code (i : native_Int) : native_String :=
  if (0 <= i && (native_char_valid (Int.toNat i))) then
    [(Int.toNat i)]
  else
    native_string_lit ""

def native_streq : native_String -> native_String -> native_Bool
  | x, y => decide (x = y)

def native_bit : native_Int -> native_Int -> native_Bool
  | x, i => (native_zeq 1 (native_mod_total (native_div_total x (native_int_pow2 i)) 2))

def native_msb : native_Int -> native_Int -> native_Bool
  | w, n => (native_bit n (native_zplus w (native_zneg 1)))

def native_binary_and : native_Int -> native_Int -> native_Int -> native_Int
  | w, n1, n2 => (native_ite (native_zeq w 0) 0 (native_piand w n1 n2))

def impl_native_pior : native_Int -> native_Int -> native_Int -> native_Int
  | w, x, y => ((BitVec.ofInt (Int.toNat w) x) ||| (BitVec.ofInt (Int.toNat w) y)).toInt

def native_binary_or : native_Int -> native_Int -> native_Int -> native_Int
  | w, n1, n2 => (native_ite (native_zeq w 0) 0 (impl_native_pior w n1 n2))

def impl_native_pixor : native_Int -> native_Int -> native_Int -> native_Int
  | w, x, y => ((BitVec.ofInt (Int.toNat w) x) ^^^ (BitVec.ofInt (Int.toNat w) y)).toInt

-- Rational arithmetic

def native_binary_xor : native_Int -> native_Int -> native_Int -> native_Int
  | w, n1, n2 => (native_ite (native_zeq w 0) 0 (impl_native_pixor w n1 n2))

def native_binary_not : native_Int -> native_Int -> native_Int
  | w, n => (native_zplus (native_int_pow2 w) (native_zneg (native_zplus n 1)))

def native_binary_max : native_Int -> native_Int
  | w => (native_zplus (native_int_pow2 w) (native_zneg 1))

def native_binary_uts : native_Int -> native_Int -> native_Int
  | w, n => (native_zplus (native_zmult 2 (native_mod_total n (native_int_pow2 (native_zplus w (native_zneg 1))))) (native_zneg n))

def native_binary_concat : native_Int -> native_Int -> native_Int -> native_Int -> native_Int
  | w1, n1, w2, n2 => (native_zplus (native_zmult n1 (native_int_pow2 w2)) n2)

def native_binary_extract : native_Int -> native_Int -> native_Int -> native_Int -> native_Int
  -- The caller masks this quotient to width x1 - x2 + 1; w and x1 are carried
  -- here only to match the signature of the operation this stands for.
  | w, n, x1, x2 => (native_div_total n (native_int_pow2 x2))

def native_int_to_nat (x : native_Int) : native_Nat :=
  (Int.toNat x)

def native_nat_to_int (x : native_Nat) : native_Int :=
  (Int.ofNat x)

def native_nateq : native_Nat -> native_Nat -> native_Bool
  | x, y => decide (x = y)

def native_natlt : native_Nat -> native_Nat -> native_Bool
  | x, y => decide (x < y)

def native_str_len : native_String -> native_Int
  | x => Int.ofNat x.length

def native_str_concat : native_String -> native_String -> native_String
  | x, y => x ++ y

def native_str_substr (s : native_String) (i n : native_Int) : native_String :=
  let len : Int := (native_str_len s)
  if i < 0 || n <= 0 || i >= len then
    []
  else
    let start : Nat := Int.toNat i
    let take  : Nat := Int.toNat (min n (len - i))
    (s.drop start).take take

def impl_native_str_indexof_rec (s t : native_String) (i fuel : Nat) : native_Int :=
  match fuel with
  | 0 => -1
  | fuel + 1 =>
      if native_string_prefix_eq t (s.drop i) then
        Int.ofNat i
      else
        impl_native_str_indexof_rec s t (i + 1) fuel

def native_str_indexof (s t : native_String) (i : native_Int) : native_Int :=
  if i < 0 then
    -1
  else
    let sLen := Int.toNat (native_str_len s)
    let start := Int.toNat i
    let tLen := Int.toNat (native_str_len t)
    if h : start + tLen <= sLen then
      impl_native_str_indexof_rec s t start (sLen - (start + tLen) + 1)
    else
      -1

def native_int_log2 : native_Int -> native_Int
  | x => Int.ofNat (Nat.log2 (Int.toNat x))

def native_zabs : native_Int -> native_Int
  | x => if x < 0 then -x else x

def native_qabs : native_Rat -> native_Rat
  | x => if x < 0 then -x else x

def native_str_lt : native_String -> native_String -> native_Bool
  | s₁, s₂ => decide (s₁ < s₂)

def native_str_from_int : native_Int -> native_String
  | i => if i < 0 then native_string_lit "" else native_string_lit (toString i)

def impl_native_char_is_digit (c : native_Char) : native_Bool :=
  48 <= c && c <= 57

def impl_native_decimal_digits_to_nat (xs : native_String) : native_Nat :=
  xs.foldl (fun acc c => 10 * acc + (c - 48)) 0

def native_str_to_int : native_String -> native_Int
  | s => match s with
          | [] => -1
          | _ => if s.all impl_native_char_is_digit then Int.ofNat (impl_native_decimal_digits_to_nat s) else -1

def impl_native_char_to_upper (c : native_Char) : native_Char :=
  if 97 <= c && c <= 122 then c - 32 else c

def native_str_to_upper : native_String -> native_String
  | s => s.map impl_native_char_to_upper

def impl_native_char_to_lower (c : native_Char) : native_Char :=
  if 65 <= c && c <= 90 then c + 32 else c

def native_str_to_lower : native_String -> native_String
  | s => s.map impl_native_char_to_lower

def native_qdiv_by_zero_id : native_String := (native_string_lit "@qdiv_by_zero")

def native_div_by_zero_id : native_String := (native_string_lit "@div_by_zero")

def native_mod_by_zero_id : native_String := (native_string_lit "@mod_by_zero")

def native_wrong_apply_sel_id (n m : native_Nat) : native_String :=
  (native_string_lit "@wrong_apply_sel_") ++ (native_string_lit (toString n)) ++ (native_string_lit "_") ++ (native_string_lit (toString m))

def native_oob_seq_nth_id : native_String := (native_string_lit "@oob_seq_nth")

def native_uconst_id : native_Nat -> native_String
  | i => (native_string_lit "@u.") ++ (native_string_lit (toString i))

def native_const_id : native_Nat -> native_String
  | i => (native_string_lit "@c.") ++ (native_string_lit (toString i))

end Eunoia
