/-
Copyright (c) 2026 Tyler B. Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tyler B. Hughes
-/
module

public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Data.Nat.Prime.Nth
public import Mathlib.Order.Lattice.Nat

import Mathlib.Tactic

/-!
# Definitions for Strong Pseudoprimes and `ψ_k`

Faithful Lean 4 formalization of the strong probable prime test (Miller–Rabin),
strong pseudoprimes to the first `k` prime bases (using Mathlib's true
`Nat.nth Nat.Prime`, not a hardcoded list), the threshold function `ψ_k`,
and Zhang's `K2` semiprime family `n = p(2p - 1)`.
-/

@[expose] public section

namespace SpspPsi20

/-- An odd integer `n ≥ 3` is a **strong probable prime** to base `a` when,
writing `n - 1 = 2^s * d` with `d` odd, either `a^d ≡ 1 [MOD n]` or
`a^(2^r * d) ≡ n - 1 [MOD n]` for some `r < s`. -/
def IsStrongProbablePrime (n a : ℕ) : Prop :=
  Odd n ∧ 3 ≤ n ∧
    ∃ s d : ℕ, Odd d ∧ n - 1 = 2 ^ s * d ∧
      (a ^ d ≡ 1 [MOD n] ∨ ∃ r < s, a ^ (2 ^ r * d) ≡ n - 1 [MOD n])

/-- An odd composite `n ≥ 3` that passes the strong probable prime test to base `a`. -/
def IsStrongPseudoprime (n a : ℕ) : Prop :=
  Odd n ∧ 3 ≤ n ∧ ¬ Nat.Prime n ∧ IsStrongProbablePrime n a

/-- An odd composite `n ≥ 3` that passes the strong probable prime test for each
of the first `k` primes `Nat.nth Nat.Prime 0, …, Nat.nth Nat.Prime (k - 1)`. -/
def IsFirstKPrimesStrongPseudoprime (k n : ℕ) : Prop :=
  Odd n ∧ 3 ≤ n ∧ ¬ Nat.Prime n ∧
    ∀ i < k, IsStrongProbablePrime n (Nat.nth Nat.Prime i)

/-- `ψ_k` (OEIS A014233): the smallest odd composite passing the strong test
for each of the first `k` prime bases. -/
noncomputable def psi (k : ℕ) : ℕ :=
  sInf { n : ℕ | IsFirstKPrimesStrongPseudoprime k n }

/-- Zhang's `K2` family: `n = p * (2 * p - 1)` where both `p` and `2 * p - 1` are prime. -/
def IsK2Number (n p : ℕ) : Prop :=
  Nat.Prime p ∧ Nat.Prime (2 * p - 1) ∧ n = p * (2 * p - 1)

/-- Uniqueness of the decomposition `m = 2^s * d` with `d` odd. -/
theorem odd_two_pow_mul_unique {s₁ d₁ s₂ d₂ : ℕ}
    (hd₁ : Odd d₁) (hd₂ : Odd d₂) (heq : 2 ^ s₁ * d₁ = 2 ^ s₂ * d₂) :
    s₁ = s₂ ∧ d₁ = d₂ := by
  induction s₁ generalizing s₂ with
  | zero =>
    cases s₂ with
    | zero =>
      simp only [pow_zero, one_mul] at heq
      exact ⟨rfl, heq⟩
    | succ s₂' =>
      exfalso
      rcases hd₁ with ⟨k, hk⟩
      rw [pow_zero, one_mul, pow_succ', mul_assoc] at heq
      omega
  | succ s₁' ih =>
    cases s₂ with
    | zero =>
      exfalso
      rcases hd₂ with ⟨k, hk⟩
      rw [pow_zero, one_mul, pow_succ', mul_assoc] at heq
      omega
    | succ s₂' =>
      rw [pow_succ', pow_succ', mul_assoc, mul_assoc] at heq
      have h' : 2 ^ s₁' * d₁ = 2 ^ s₂' * d₂ := mul_left_cancel₀ (by norm_num) heq
      obtain ⟨hs, hd⟩ := ih h'
      exact ⟨congrArg Nat.succ hs, hd⟩

/-- Existence and uniqueness of the decomposition `m = 2^s * d` with `d` odd
for every positive `m : ℕ`. -/
theorem exists_unique_two_pow_mul_odd {m : ℕ} (hm : 0 < m) :
    ∃! sd : ℕ × ℕ, Odd sd.2 ∧ m = 2 ^ sd.1 * sd.2 := by
  have hex : ∀ k : ℕ, 0 < k → ∃ sd : ℕ × ℕ, Odd sd.2 ∧ k = 2 ^ sd.1 * sd.2 := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro hk
      by_cases hpar : k % 2 = 1
      · refine ⟨(0, k), ⟨k / 2, by omega⟩, by simp⟩
      · have hdiv_pos : 0 < k / 2 := by omega
        have hdiv_lt : k / 2 < k := Nat.div_lt_self hk (by norm_num)
        obtain ⟨⟨s, d⟩, hd, heq⟩ := ih (k / 2) hdiv_lt hdiv_pos
        refine ⟨(s + 1, d), hd, ?_⟩
        rw [pow_succ', mul_assoc, ← heq]
        omega
  obtain ⟨sd, hsd⟩ := hex m hm
  refine ⟨sd, hsd, ?_⟩
  rintro ⟨s', d'⟩ ⟨hd', heq'⟩
  obtain ⟨hs, hd⟩ := odd_two_pow_mul_unique hd' hsd.1 (heq'.symm.trans hsd.2)
  exact Prod.ext hs hd

/-- Equivalent characterization of `IsStrongProbablePrime` for any explicit
decomposition `n - 1 = 2^s * d` with `d` odd. -/
theorem isStrongProbablePrime_iff_of_decomp {n a s d : ℕ}
    (hodd : Odd n) (h3 : 3 ≤ n) (hd : Odd d) (hdecomp : n - 1 = 2 ^ s * d) :
    IsStrongProbablePrime n a ↔
      (a ^ d ≡ 1 [MOD n] ∨ ∃ r < s, a ^ (2 ^ r * d) ≡ n - 1 [MOD n]) := by
  constructor
  · rintro ⟨_, _, s', d', hd', hdecomp', h⟩
    obtain ⟨rfl, rfl⟩ := odd_two_pow_mul_unique hd' hd (hdecomp'.symm.trans hdecomp)
    exact h
  · intro h
    exact ⟨hodd, h3, s, d, hd, hdecomp, h⟩

/-- For `n ≥ 2`, `(n - 1)^2 ≡ 1 [MOD n]`. -/
theorem sq_sub_one_modEq_one {n : ℕ} (hn : 2 ≤ n) : (n - 1) ^ 2 ≡ 1 [MOD n] := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  change (k + 1) ^ 2 % (k + 2) = 1 % (k + 2)
  have h : (k + 1) ^ 2 = (k + 2) * k + 1 := by ring
  rw [h, Nat.mul_add_mod]

/-- Every strong probable prime to base `a` satisfies the Fermat congruence
`a^(n - 1) ≡ 1 [MOD n]`. -/
theorem isStrongProbablePrime_implies_fermat {n a : ℕ}
    (h : IsStrongProbablePrime n a) : a ^ (n - 1) ≡ 1 [MOD n] := by
  rcases h with ⟨_, h3, s, d, _, hdecomp, hbase | ⟨r, hr, hneg⟩⟩
  · rw [hdecomp, mul_comm, pow_mul]
    simpa [one_pow] using hbase.pow (2 ^ s)
  · have hsq : a ^ (2 ^ (r + 1) * d) ≡ 1 [MOD n] := by
      have hexp : 2 ^ (r + 1) * d = (2 ^ r * d) * 2 := by
        rw [pow_succ]; ring
      rw [hexp, pow_mul]
      exact (hneg.pow 2).trans (sq_sub_one_modEq_one (by omega))
    have hrem : 2 ^ s * d = (2 ^ (r + 1) * d) * 2 ^ (s - (r + 1)) := by
      have hs : r + 1 + (s - (r + 1)) = s := by omega
      calc
        2 ^ s * d = 2 ^ (r + 1 + (s - (r + 1))) * d := by rw [hs]
        _ = (2 ^ (r + 1) * 2 ^ (s - (r + 1))) * d := by rw [pow_add]
        _ = (2 ^ (r + 1) * d) * 2 ^ (s - (r + 1)) := by ring
    rw [hdecomp, hrem, pow_mul]
    simpa [one_pow] using hsq.pow (2 ^ (s - (r + 1)))

/-- Passing the first `k` prime bases implies passing the first `j ≤ k` prime bases. -/
theorem isFirstKPrimesStrongPseudoprime_mono {j k n : ℕ} (hjk : j ≤ k)
    (hk : IsFirstKPrimesStrongPseudoprime k n) :
    IsFirstKPrimesStrongPseudoprime j n :=
  ⟨hk.1, hk.2.1, hk.2.2.1, fun i hi => hk.2.2.2 i (lt_of_lt_of_le hi hjk)⟩

/-- Any explicit `k`-base strong pseudoprime `n` gives an upper bound `ψ_k ≤ n`. -/
theorem psi_le_of_spsp {k n : ℕ} (h : IsFirstKPrimesStrongPseudoprime k n) :
    psi k ≤ n :=
  Nat.sInf_le h

/-- Monotonicity of `ψ_k`: if `j ≤ k` and there exists at least one `k`-base
strong pseudoprime, then `ψ_j ≤ ψ_k`. -/
theorem psi_mono {j k : ℕ} (hjk : j ≤ k)
    (hne : { n : ℕ | IsFirstKPrimesStrongPseudoprime k n }.Nonempty) :
    psi j ≤ psi k := by
  have hmem : IsFirstKPrimesStrongPseudoprime k (psi k) := Nat.sInf_mem hne
  exact Nat.sInf_le (isFirstKPrimesStrongPseudoprime_mono hjk hmem)

/-- Every `K2` number `n = p(2p - 1)` is composite. -/
theorem isK2Number_not_prime {n p : ℕ} (h : IsK2Number n p) : ¬ Nat.Prime n := by
  rcases h with ⟨hp, hq, rfl⟩
  exact Nat.not_prime_mul hp.one_lt.ne' hq.one_lt.ne'

end SpspPsi20

end
