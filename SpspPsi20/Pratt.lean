/-
Copyright (c) 2026 Tyler B. Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tyler B. Hughes
-/
module

public import SpspPsi20.Defs
public import Mathlib.NumberTheory.LucasPrimality
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Nat.Log
public import Mathlib.Data.Nat.Count
public import Mathlib.Data.Nat.Prime.Nth

import Mathlib.Tactic

/-!
# Verified Modular Exponentiation, Pratt Primality Engine, and First 21 Primes

Provides:
1. Structurally recursive binary modular exponentiation (`modPowAux`, `modPowFuel`, `modPow`)
   proved equal to `a ^ e % m`. Because recursion is structural on `fuel : ℕ` and
   all arithmetic uses Lean 4 kernel GMP primitives, `modPowFuel` reduces via `rfl`/`decide`
   on 37-digit moduli in milliseconds with zero `native_decide`.
2. Soundness of Pratt primality certificates (`prime_of_pratt`) via Mathlib's `lucas_primality`.
3. Verified decision procedure `sprpCheck` for `IsStrongProbablePrime`.
4. Exact table of the first 21 primes `Nat.nth Nat.Prime 0, …, Nat.nth Nat.Prime 20`
   proved from Mathlib's `Nat.nth Nat.Prime`.
-/

@[expose] public section

namespace SpspPsi20

/-- Tail-recursive binary modular exponentiation, structurally recursive on `k : ℕ`. -/
def modPowAux : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, acc, _, _, _ => acc
  | k + 1, acc, base, exp, m =>
    if exp = 0 then acc
    else
      let acc' := if exp % 2 = 1 then (acc * base) % m else acc
      modPowAux k acc' ((base * base) % m) (exp / 2) m

/-- Binary modular exponentiation with explicit step bound `fuel`. -/
def modPowFuel (fuel a e m : ℕ) : ℕ :=
  modPowAux fuel (1 % m) (a % m) e m

/-- Unconditional binary modular exponentiation `a ^ e % m`. -/
def modPow (a e m : ℕ) : ℕ :=
  modPowFuel (Nat.log2 e + 1) a e m

/-- Loop invariant for `modPowAux`. -/
theorem modPowAux_eq : ∀ (k acc base exp m : ℕ),
    exp < 2 ^ k →
    modPowAux k (acc % m) base exp m = (acc * base ^ exp) % m
  | 0, acc, base, exp, m, hexp => by
    have h0 : exp = 0 := by simpa using hexp
    subst h0
    simp [modPowAux]
  | k + 1, acc, base, exp, m, hexp => by
    unfold modPowAux
    split_ifs with h0 hodd
    · subst h0
      simp
    · have hdiv : exp / 2 < 2 ^ k := by
        rw [pow_succ'] at hexp
        omega
      have hacc : (acc % m * base) % m = (acc * base) % m := by
        rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
      rw [hacc, modPowAux_eq k (acc * base) ((base * base) % m) (exp / 2) m hdiv]
      have hpow : ((base * base) % m) ^ (exp / 2) % m = (base * base) ^ (exp / 2) % m :=
        (Nat.pow_mod (base * base) (exp / 2) m).symm
      rw [Nat.mul_mod, hpow, ← Nat.mul_mod]
      have hexp_eq : exp = 2 * (exp / 2) + 1 := by omega
      congr 1
      calc
        acc * base * (base * base) ^ (exp / 2)
            = acc * base * (base ^ 2) ^ (exp / 2) := by rw [sq]
        _ = acc * base * base ^ (2 * (exp / 2)) := by rw [← pow_mul]
        _ = acc * (base ^ (2 * (exp / 2)) * base) := by ring
        _ = acc * base ^ (2 * (exp / 2) + 1) := by rw [← pow_succ]
        _ = acc * base ^ exp := by rw [← hexp_eq]
    · have hdiv : exp / 2 < 2 ^ k := by
        rw [pow_succ'] at hexp
        omega
      rw [modPowAux_eq k acc ((base * base) % m) (exp / 2) m hdiv]
      have hpow : ((base * base) % m) ^ (exp / 2) % m = (base * base) ^ (exp / 2) % m :=
        (Nat.pow_mod (base * base) (exp / 2) m).symm
      rw [Nat.mul_mod, hpow, ← Nat.mul_mod]
      have hexp_eq : exp = 2 * (exp / 2) := by omega
      congr 1
      calc
        acc * (base * base) ^ (exp / 2)
            = acc * (base ^ 2) ^ (exp / 2) := by rw [sq]
        _ = acc * base ^ (2 * (exp / 2)) := by rw [← pow_mul]
        _ = acc * base ^ exp := by rw [← hexp_eq]

/-- Correctness of `modPowFuel` whenever `e < 2 ^ fuel`. -/
theorem modPowFuel_eq (fuel a e m : ℕ) (he : e < 2 ^ fuel) :
    modPowFuel fuel a e m = a ^ e % m := by
  unfold modPowFuel
  rw [modPowAux_eq fuel 1 (a % m) e m he, one_mul, ← Nat.pow_mod]

/-- Congruence form of `modPowFuel_eq`. -/
theorem modPowFuel_modEq (fuel a e m : ℕ) (he : e < 2 ^ fuel) :
    a ^ e ≡ modPowFuel fuel a e m [MOD m] := by
  rw [modPowFuel_eq fuel a e m he]
  exact (Nat.mod_modEq (a ^ e) m).symm

/-- Every `e : ℕ` satisfies `e < 2 ^ (Nat.log2 e + 1)`. -/
theorem lt_two_pow_log2_succ (e : ℕ) : e < 2 ^ (Nat.log2 e + 1) := by
  rw [Nat.log2_eq_log_two]
  exact Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) e

/-- Unconditional correctness of `modPow`. -/
theorem modPow_eq (a e m : ℕ) : modPow a e m = a ^ e % m :=
  modPowFuel_eq (Nat.log2 e + 1) a e m (lt_two_pow_log2_succ e)

/-- Unconditional congruence form of `modPow`. -/
theorem modPow_modEq (a e m : ℕ) : a ^ e ≡ modPow a e m [MOD m] :=
  modPowFuel_modEq (Nat.log2 e + 1) a e m (lt_two_pow_log2_succ e)

/-- Bridge between `(a : ZMod p) ^ e = 1` and `a ^ e % p = 1` for `1 < p`. -/
theorem zmod_pow_eq_one_iff {p a e : ℕ} (hp : 1 < p) :
    ((a : ZMod p) ^ e = 1) ↔ a ^ e % p = 1 := by
  have : NeZero p := ⟨by omega⟩
  rw [← Nat.cast_pow, ← Nat.cast_one, ZMod.natCast_eq_natCast_iff]
  change a ^ e % p = 1 % p ↔ a ^ e % p = 1
  rw [Nat.mod_eq_of_lt hp]

/-- If a prime `q` divides the product of a list of primes `fs`, then `q ∈ fs`. -/
theorem mem_of_prime_dvd_list_prod {q : ℕ} {fs : List ℕ}
    (hq : Nat.Prime q) (hprime : ∀ r ∈ fs, Nat.Prime r) (hdvd : q ∣ fs.prod) :
    q ∈ fs := by
  induction fs with
  | nil =>
    simp only [List.prod_nil] at hdvd
    exact absurd hdvd hq.not_dvd_one
  | cons r rs ih =>
    simp only [List.prod_cons] at hdvd
    rcases hq.dvd_mul.mp hdvd with hqr | hqrs
    · have hr : Nat.Prime r := hprime r (by simp)
      have heq : q = r := (Nat.prime_dvd_prime_iff_eq hq hr).mp hqr
      simp [heq]
    · have hmem : q ∈ rs := ih (fun x hx => hprime x (by simp [hx])) hqrs
      simp [hmem]

/-- Soundness of a Pratt primality certificate via Mathlib's `lucas_primality`.
Given a list `fs` of primes whose product is `p - 1`, and a primitive-root witness `a`
checked by `modPowFuel`, `p` is prime. -/
theorem prime_of_pratt (p a fuel : ℕ) (fs : List ℕ)
    (hp : 2 ≤ p)
    (hfuel : p - 1 < 2 ^ fuel)
    (hprod : fs.prod = p - 1)
    (hprime : ∀ q ∈ fs, Nat.Prime q)
    (hfermat : modPowFuel fuel a (p - 1) p = 1)
    (horder : ∀ q ∈ fs, modPowFuel fuel a ((p - 1) / q) p ≠ 1) :
    Nat.Prime p := by
  apply lucas_primality p (a : ZMod p)
  · rw [zmod_pow_eq_one_iff (by omega), ← modPowFuel_eq fuel a (p - 1) p hfuel]
    exact hfermat
  · intro q hq hqd
    have hqmem : q ∈ fs := mem_of_prime_dvd_list_prod hq hprime (hprod ▸ hqd)
    have hlt : (p - 1) / q < 2 ^ fuel := lt_of_le_of_lt (Nat.div_le_self _ _) hfuel
    rw [ne_eq, zmod_pow_eq_one_iff (by omega),
      ← modPowFuel_eq fuel a ((p - 1) / q) p hlt]
    exact horder q hqmem

/-- Decidable strong probable prime check using `modPowFuel`. -/
def sprpCheck (fuel n d s a : ℕ) : Bool :=
  decide (modPowFuel fuel a d n = 1) ||
    (List.range s).any (fun r => decide (modPowFuel fuel a (2 ^ r * d) n = n - 1))

/-- Exact equivalence between `sprpCheck` and `IsStrongProbablePrime`. -/
theorem sprpCheck_eq_true_iff {fuel n d s a : ℕ}
    (hodd : Odd n) (h3 : 3 ≤ n) (hd : Odd d) (hdecomp : n - 1 = 2 ^ s * d)
    (hfuel : n - 1 < 2 ^ fuel) :
    sprpCheck fuel n d s a = true ↔ IsStrongProbablePrime n a := by
  rw [isStrongProbablePrime_iff_of_decomp hodd h3 hd hdecomp]
  simp only [sprpCheck, Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true, List.mem_range]
  have hd_lt : d < 2 ^ fuel := by
    have h1 : 1 ≤ 2 ^ s := Nat.one_le_two_pow
    have hle : d ≤ 2 ^ s * d := Nat.le_mul_of_pos_left d (by omega)
    omega
  have h1mod : 1 % n = 1 := Nat.mod_eq_of_lt (by omega)
  have hnm1mod : (n - 1) % n = n - 1 := Nat.mod_eq_of_lt (by omega)
  constructor
  · rintro (h1 | ⟨r, hr, h2⟩)
    · left
      change a ^ d % n = 1 % n
      rw [h1mod, ← modPowFuel_eq fuel a d n hd_lt]
      exact h1
    · right
      refine ⟨r, hr, ?_⟩
      have hpow_lt : 2 ^ r * d < 2 ^ fuel := by
        have hpow_le : 2 ^ r ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) (le_of_lt hr)
        have hle : 2 ^ r * d ≤ 2 ^ s * d := Nat.mul_le_mul_right d hpow_le
        omega
      change a ^ (2 ^ r * d) % n = (n - 1) % n
      rw [hnm1mod, ← modPowFuel_eq fuel a (2 ^ r * d) n hpow_lt]
      exact h2
  · rintro (h1 | ⟨r, hr, h2⟩)
    · left
      rw [modPowFuel_eq fuel a d n hd_lt]
      change a ^ d % n = 1 % n at h1
      rw [h1mod] at h1
      exact h1
    · right
      refine ⟨r, hr, ?_⟩
      have hpow_lt : 2 ^ r * d < 2 ^ fuel := by
        have hpow_le : 2 ^ r ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) (le_of_lt hr)
        have hle : 2 ^ r * d ≤ 2 ^ s * d := Nat.mul_le_mul_right d hpow_le
        omega
      rw [modPowFuel_eq fuel a (2 ^ r * d) n hpow_lt]
      change a ^ (2 ^ r * d) % n = (n - 1) % n at h2
      rw [hnm1mod] at h2
      exact h2

/-- Computable prime counting function `π(n)` (count of primes strictly below `n`). -/
def countPrimes : ℕ → ℕ
  | 0 => 0
  | n + 1 => countPrimes n + if Nat.Prime n then 1 else 0

/-- `countPrimes n` agrees with Mathlib's `Nat.count Nat.Prime n`. -/
theorem countPrimes_eq_count (n : ℕ) : countPrimes n = Nat.count Nat.Prime n := by
  induction n with
  | zero => simp [countPrimes, Nat.count_zero]
  | succ n ih =>
    simp only [countPrimes, Nat.count_succ, ih]

/-- Determine `Nat.nth Nat.Prime i` from primality of `p` and `countPrimes p = i`. -/
theorem nth_prime_of_countPrimes {i p : ℕ} (hp : Nat.Prime p)
    (hc : countPrimes p = i) : Nat.nth Nat.Prime i = p := by
  rw [← hc, countPrimes_eq_count]
  exact Nat.nth_count hp

/-- The first 21 prime numbers `p_0, …, p_20` (2 through 73). -/
def first21Primes : List ℕ :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73]

/-- Exact values of `Nat.nth Nat.Prime i` for all `i = 0, …, 20` (2 through 73),
proved from Mathlib's `Nat.nth Nat.Prime` definition. -/
theorem nth_prime_table :
    ∀ i : ℕ, (hi : i < first21Primes.length) →
      Nat.nth Nat.Prime i = first21Primes[i] := by
  have hcheck :
      ∀ i : Fin first21Primes.length,
        Nat.Prime first21Primes[i.val] ∧ countPrimes first21Primes[i.val] = i.val := by
    decide
  intro i hi
  exact nth_prime_of_countPrimes (hcheck ⟨i, hi⟩).1 (hcheck ⟨i, hi⟩).2

/-- The 21st prime (0-indexed `i = 20`) is `73`. -/
theorem nth_prime_20 : Nat.nth Nat.Prime 20 = 73 :=
  nth_prime_table 20 (by decide)

/-- Batch checker theorem: if `first21Primes.take k` passes `sprpCheck`, then
`n` passes the strong probable prime test for every `Nat.nth Nat.Prime i` with `i < k`. -/
theorem forall_nth_prime_sprp_of_all {fuel n d s k : ℕ}
    (hk : k ≤ first21Primes.length)
    (hodd : Odd n) (h3 : 3 ≤ n) (hd : Odd d) (hdecomp : n - 1 = 2 ^ s * d)
    (hfuel : n - 1 < 2 ^ fuel)
    (hall : (first21Primes.take k).all (sprpCheck fuel n d s) = true) :
    ∀ i < k, IsStrongProbablePrime n (Nat.nth Nat.Prime i) := by
  intro i hi
  have hi21 : i < first21Primes.length := lt_of_lt_of_le hi hk
  rw [nth_prime_table i hi21, ← sprpCheck_eq_true_iff hodd h3 hd hdecomp hfuel]
  have hmem : first21Primes[i] ∈ first21Primes.take k := by
    have hlen : i < (first21Primes.take k).length := by
      simp [Nat.min_eq_left hk, hi]
    have hget : (first21Primes.take k)[i] = first21Primes[i] := List.getElem_take
    rw [← hget]
    exact List.getElem_mem hlen
  exact List.all_eq_true.mp hall _ hmem

end SpspPsi20

end
