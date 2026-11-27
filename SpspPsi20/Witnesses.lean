/-
Copyright (c) 2026 Tyler B. Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tyler B. Hughes
-/
module

public import SpspPsi20.Defs
public import SpspPsi20.Pratt

import Mathlib.Tactic

/-!
# Two Explicit 37-Digit 20-Base Strong Pseudoprimes (`ψ_20 ≤ n₁`)

Unconditional Lean 4 formalization of the two explicit 37-digit `K2` strong pseudoprimes
discovered in `(10^36, 10^37]` (`stable-spsp-psi20`):

- `p₁ = 1113813905784150541`, `q₁ = 2 * p₁ - 1 = 2227627811568301081`,
  `n₁ = p₁ * q₁ = 2481162833436289154832260656117034821`
- `p₂ = 1726253494836549181`, `q₂ = 2 * p₂ - 1 = 3452506989673098361`,
  `n₂ = p₂ * q₂ = 5959902256870799858089729225626992341`

Every primality proof is an unconditional Pratt certificate checked via `prime_of_pratt`
(backed by Mathlib's `lucas_primality`), and every strong probable prime check uses the
verified `sprpCheck` engine with kernel GMP arithmetic (zero `native_decide`, zero `sorry`).
-/

@[expose] public section

namespace SpspPsi20

/-! ## Explicit Witnesses -/

/-- First `K2` prime factor `p₁`. -/
def p₁ : ℕ := 1113813905784150541

/-- Companion prime `q₁ = 2 * p₁ - 1 = 2227627811568301081`. -/
def q₁ : ℕ := 2 * p₁ - 1

/-- First 37-digit 20-base strong pseudoprime `n₁ = p₁ * q₁`. -/
def n₁ : ℕ := p₁ * q₁

/-- Second `K2` prime factor `p₂`. -/
def p₂ : ℕ := 1726253494836549181

/-- Companion prime `q₂ = 2 * p₂ - 1 = 3452506989673098361`. -/
def q₂ : ℕ := 2 * p₂ - 1

/-- Second 37-digit 20-base strong pseudoprime `n₂ = p₂ * q₂`. -/
def n₂ : ℕ := p₂ * q₂

/-- Exact decimal value of `n₁`. -/
theorem n₁_eq : n₁ = 2481162833436289154832260656117034821 := by rfl

/-- Exact decimal value of `n₂`. -/
theorem n₂_eq : n₂ = 5959902256870799858089729225626992341 := by rfl

/-- Strict ordering between the two 37-digit witnesses. -/
theorem n₁_lt_n₂ : n₁ < n₂ := by decide

/-- `n₁` is a 37-digit integer lying in `(10^36, 10^37]`. -/
theorem n₁_in_band : 10 ^ 36 < n₁ ∧ n₁ ≤ 10 ^ 37 := by
  constructor <;> decide

/-- `n₂` is a 37-digit integer lying in `(10^36, 10^37]`. -/
theorem n₂_in_band : 10 ^ 36 < n₂ ∧ n₂ ≤ 10 ^ 37 := by
  constructor <;> decide

/-! ## Pratt Primality Certificates for `p₁`, `q₁`, `p₂`, `q₂` -/

set_option maxRecDepth 4096

private theorem prime_13697 : Nat.Prime 13697 :=
  prime_of_pratt 13697 3 16 [2, 2, 2, 2, 2, 2, 2, 107]
    (by decide) (by decide) (by rfl)
    (by intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num)
    (by rfl) (by decide)

private theorem prime_82183 : Nat.Prime 82183 :=
  prime_of_pratt 82183 21 17 [2, 3, 13697]
    (by decide) (by decide) (by rfl)
    (by intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl
        · norm_num
        · norm_num
        · exact prime_13697)
    (by rfl) (by decide)

private theorem prime_634511 : Nat.Prime 634511 :=
  prime_of_pratt 634511 11 20 [2, 5, 107, 593]
    (by decide) (by decide) (by rfl)
    (by intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl | rfl <;> norm_num)
    (by rfl) (by decide)

private theorem prime_620551759 : Nat.Prime 620551759 :=
  prime_of_pratt 620551759 6 30 [2, 3, 163, 634511]
    (by decide) (by decide) (by rfl)
    (by intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl | rfl
        · norm_num
        · norm_num
        · norm_num
        · exact prime_634511)
    (by rfl) (by decide)

private theorem prime_18563565096402509 : Nat.Prime 18563565096402509 :=
  prime_of_pratt 18563565096402509 2 55 [2, 2, 7, 13, 82183, 620551759]
    (by decide) (by decide) (by rfl)
    (by intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
        · norm_num
        · norm_num
        · norm_num
        · norm_num
        · exact prime_82183
        · exact prime_620551759)
    (by rfl) (by decide)

/-- Pratt primality proof that `p₁ = 1113813905784150541` is prime. -/
theorem p₁_prime : Nat.Prime p₁ :=
  prime_of_pratt p₁ 2 61 [2, 2, 3, 5, 18563565096402509]
    (by decide) (by decide) (by rfl)
    (by intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl | rfl | rfl
        · norm_num
        · norm_num
        · norm_num
        · norm_num
        · exact prime_18563565096402509)
    (by rfl) (by decide)

/-- Pratt primality proof that `q₁ = 2 * p₁ - 1 = 2227627811568301081` is prime. -/
theorem q₁_prime : Nat.Prime q₁ :=
  prime_of_pratt q₁ 101 62 [2, 2, 2, 3, 5, 18563565096402509]
    (by decide) (by decide) (by rfl)
    (by intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
        · norm_num
        · norm_num
        · norm_num
        · norm_num
        · norm_num
        · exact prime_18563565096402509)
    (by rfl) (by decide)

/-- `n₁ = p₁ * (2 * p₁ - 1)` is a `K2` number. -/
theorem n₁_isK2 : IsK2Number n₁ p₁ :=
  ⟨p₁_prime, q₁_prime, rfl⟩

/-- `n₁` is composite. -/
theorem n₁_not_prime : ¬ Nat.Prime n₁ :=
  isK2Number_not_prime n₁_isK2

private theorem prime_52543 : Nat.Prime 52543 :=
  prime_of_pratt 52543 3 16 [2, 3, 3, 3, 7, 139]
    (by decide) (by decide) (by rfl)
    (by intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num)
    (by rfl) (by decide)

private theorem prime_2101721 : Nat.Prime 2101721 :=
  prime_of_pratt 2101721 3 22 [2, 2, 2, 5, 52543]
    (by decide) (by decide) (by rfl)
    (by intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl | rfl | rfl
        · norm_num
        · norm_num
        · norm_num
        · norm_num
        · exact prime_52543)
    (by rfl) (by decide)

private theorem prime_158955202102813 : Nat.Prime 158955202102813 :=
  prime_of_pratt 158955202102813 2 48 [2, 2, 3, 61, 277, 373, 2101721]
    (by decide) (by decide) (by rfl)
    (by intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · norm_num
        · norm_num
        · norm_num
        · norm_num
        · norm_num
        · norm_num
        · exact prime_2101721)
    (by rfl) (by decide)

/-- Pratt primality proof that `p₂ = 1726253494836549181` is prime. -/
theorem p₂_prime : Nat.Prime p₂ :=
  prime_of_pratt p₂ 10 61 [2, 2, 3, 5, 181, 158955202102813]
    (by decide) (by decide) (by rfl)
    (by intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
        · norm_num
        · norm_num
        · norm_num
        · norm_num
        · norm_num
        · exact prime_158955202102813)
    (by rfl) (by decide)

/-- Pratt primality proof that `q₂ = 2 * p₂ - 1 = 3452506989673098361` is prime. -/
theorem q₂_prime : Nat.Prime q₂ :=
  prime_of_pratt q₂ 89 62 [2, 2, 2, 3, 5, 181, 158955202102813]
    (by decide) (by decide) (by rfl)
    (by intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · norm_num
        · norm_num
        · norm_num
        · norm_num
        · norm_num
        · norm_num
        · exact prime_158955202102813)
    (by rfl) (by decide)

/-- `n₂ = p₂ * (2 * p₂ - 1)` is a `K2` number. -/
theorem n₂_isK2 : IsK2Number n₂ p₂ :=
  ⟨p₂_prime, q₂_prime, rfl⟩

/-- `n₂` is composite. -/
theorem n₂_not_prime : ¬ Nat.Prime n₂ :=
  isK2Number_not_prime n₂_isK2

/-! ## 20-Base Strong Pseudoprime Proofs and Base-73 Failure -/

private def d₁ : ℕ := 620290708359072288708065164029258705
private def d₂ : ℕ := 1489975564217699964522432306406748085

private theorem n₁_odd : Odd n₁ := ⟨(n₁ - 1) / 2, by decide⟩
private theorem d₁_odd : Odd d₁ := ⟨(d₁ - 1) / 2, by decide⟩
private theorem n₁_decomp : n₁ - 1 = 2 ^ 2 * d₁ := by rfl

private theorem n₂_odd : Odd n₂ := ⟨(n₂ - 1) / 2, by decide⟩
private theorem d₂_odd : Odd d₂ := ⟨(d₂ - 1) / 2, by decide⟩
private theorem n₂_decomp : n₂ - 1 = 2 ^ 2 * d₂ := by rfl

/-- `n₁` is a strong pseudoprime to each of the first 20 prime bases (`2, …, 71`). -/
theorem n₁_spsp_20 : IsFirstKPrimesStrongPseudoprime 20 n₁ :=
  ⟨n₁_odd, by decide, n₁_not_prime,
    forall_nth_prime_sprp_of_all (fuel := 124) (by decide) n₁_odd (by decide) d₁_odd n₁_decomp
      (by decide) (by rfl)⟩

/-- `n₁` fails the strong probable prime test to the 21st prime base `73`. -/
theorem n₁_fails_73 : ¬ IsStrongProbablePrime n₁ 73 := by
  rw [← sprpCheck_eq_true_iff (fuel := 124) n₁_odd (by decide) d₁_odd n₁_decomp (by decide)]
  decide

/-- `n₁` is not a 21-base strong pseudoprime. -/
theorem n₁_not_spsp_21 : ¬ IsFirstKPrimesStrongPseudoprime 21 n₁ := by
  intro h
  have h20 : IsStrongProbablePrime n₁ (Nat.nth Nat.Prime 20) := h.2.2.2 20 (by omega)
  rw [nth_prime_20] at h20
  exact n₁_fails_73 h20

/-- `n₂` is a strong pseudoprime to each of the first 20 prime bases (`2, …, 71`). -/
theorem n₂_spsp_20 : IsFirstKPrimesStrongPseudoprime 20 n₂ :=
  ⟨n₂_odd, by decide, n₂_not_prime,
    forall_nth_prime_sprp_of_all (fuel := 124) (by decide) n₂_odd (by decide) d₂_odd n₂_decomp
      (by decide) (by rfl)⟩

/-- `n₂` fails the strong probable prime test to the 21st prime base `73`. -/
theorem n₂_fails_73 : ¬ IsStrongProbablePrime n₂ 73 := by
  rw [← sprpCheck_eq_true_iff (fuel := 124) n₂_odd (by decide) d₂_odd n₂_decomp (by decide)]
  decide

/-- `n₂` is not a 21-base strong pseudoprime. -/
theorem n₂_not_spsp_21 : ¬ IsFirstKPrimesStrongPseudoprime 21 n₂ := by
  intro h
  have h20 : IsStrongProbablePrime n₂ (Nat.nth Nat.Prime 20) := h.2.2.2 20 (by omega)
  rw [nth_prime_20] at h20
  exact n₂_fails_73 h20

/-! ## Upper Bounds on `ψ_20` and `ψ_k` for `k ≤ 20` -/

/-- Main upper bound: `ψ_20 ≤ n₁ = 2481162833436289154832260656117034821`. -/
theorem psi_20_le_n₁ : psi 20 ≤ n₁ :=
  psi_le_of_spsp n₁_spsp_20

/-- Second upper bound: `ψ_20 ≤ n₂ = 5959902256870799858089729225626992341`. -/
theorem psi_20_le_n₂ : psi 20 ≤ n₂ :=
  psi_le_of_spsp n₂_spsp_20

/-- Monotonicity corollary: `ψ_k ≤ n₁` for every `k ≤ 20`. -/
theorem psi_le_n₁_of_le_20 : ∀ k ≤ 20, psi k ≤ n₁ := by
  intro k hk
  exact le_trans (psi_mono hk ⟨n₁, n₁_spsp_20⟩) psi_20_le_n₁

/-! ## Hand Cases and False Variants from the Charter and Run Record -/

/-- Charter hand case: `2047 = 23 * 89` is a strong pseudoprime to base `2`. -/
theorem spsp_2047_base2 : IsStrongPseudoprime 2047 2 := by
  have hodd : Odd 2047 := ⟨1023, by norm_num⟩
  have hd : Odd 1023 := ⟨511, by norm_num⟩
  have hnp : ¬ Nat.Prime 2047 := by
    intro hp
    have hdvd : 23 ∣ 2047 := ⟨89, by norm_num⟩
    rcases hp.eq_one_or_self_of_dvd 23 hdvd with h | h <;> omega
  refine ⟨hodd, by norm_num, hnp, ?_⟩
  rw [← sprpCheck_eq_true_iff (fuel := 12) (s := 1) hodd (by norm_num) hd (by norm_num) (by decide)]
  rfl

/-- Charter hand case: `2047` fails the strong probable prime test to base `3`. -/
theorem not_spsp_2047_base3 : ¬ IsStrongProbablePrime 2047 3 := by
  have hodd : Odd 2047 := ⟨1023, by norm_num⟩
  have hd : Odd 1023 := ⟨511, by norm_num⟩
  rw [← sprpCheck_eq_true_iff (fuel := 12) (s := 1) hodd (by norm_num) hd (by norm_num) (by decide)]
  decide

/-- Record hand case: `15 = 3 * 5` is a `K2` number (`p = 3`), and fails base `2`. -/
theorem k2_15_not_spsp2 : IsK2Number 15 3 ∧ ¬ IsStrongProbablePrime 15 2 := by
  constructor
  · exact ⟨by norm_num, by norm_num, by rfl⟩
  · have hodd : Odd 15 := ⟨7, by norm_num⟩
    have hd : Odd 7 := ⟨3, by norm_num⟩
    rw [← sprpCheck_eq_true_iff (fuel := 4) (s := 1) hodd (by norm_num) hd (by norm_num) (by decide)]
    decide

/-- Record false variant: `n₁ + 2` fails the strong test at base `2`. -/
theorem n₁_plus2_fails_2 : ¬ IsStrongProbablePrime (n₁ + 2) 2 := by
  have hodd : Odd (n₁ + 2) := ⟨(n₁ + 1) / 2, by decide⟩
  have hd : Odd 1240581416718144577416130328058517411 :=
    ⟨620290708359072288708065164029258705, by decide⟩
  rw [← sprpCheck_eq_true_iff (fuel := 124) (s := 1) hodd (by decide) hd (by rfl) (by decide)]
  decide

/-- Record false variant: `n₂ + 2` fails the strong test at base `2`. -/
theorem n₂_plus2_fails_2 : ¬ IsStrongProbablePrime (n₂ + 2) 2 := by
  have hodd : Odd (n₂ + 2) := ⟨(n₂ + 1) / 2, by decide⟩
  have hd : Odd 2979951128435399929044864612813496171 :=
    ⟨1489975564217699964522432306406748085, by decide⟩
  rw [← sprpCheck_eq_true_iff (fuel := 124) (s := 1) hodd (by decide) hd (by rfl) (by decide)]
  decide

/-- Exact bit length of `n₁` (121 bits: `2^120 < n₁ < 2^121`). -/
theorem n₁_bit_bounds : 2 ^ 120 < n₁ ∧ n₁ < 2 ^ 121 := by
  constructor <;> decide

/-- Exact bit length of `n₂` (123 bits: `2^122 < n₂ < 2^123`). -/
theorem n₂_bit_bounds : 2 ^ 122 < n₂ ∧ n₂ < 2 ^ 123 := by
  constructor <;> decide

/-- `n₁` still passes the Fermat test at base `73`. -/
theorem n₁_fermat_73 : 73 ^ (n₁ - 1) ≡ 1 [MOD n₁] := by
  have h : modPowFuel 124 73 (n₁ - 1) n₁ = 1 := by rfl
  simpa [h] using modPowFuel_modEq 124 73 (n₁ - 1) n₁ (by decide)

/-- `n₂` still passes the Fermat test at base `73`. -/
theorem n₂_fermat_73 : 73 ^ (n₂ - 1) ≡ 1 [MOD n₂] := by
  have h : modPowFuel 124 73 (n₂ - 1) n₂ = 1 := by rfl
  simpa [h] using modPowFuel_modEq 124 73 (n₂ - 1) n₂ (by decide)

/-- Combined Theorem 1: both 37-digit `K2` witnesses `n₁` (121 bits) and `n₂` (123 bits)
pass the first 20 prime bases, fail the strong test at base 73 while passing Fermat at 73,
and yield `ψ_20 ≤ n₁ < 2^121` and `∀ k ≤ 20, ψ_k ≤ n₁`. -/
theorem main_two_witnesses :
    IsK2Number n₁ p₁ ∧ (10 ^ 36 < n₁ ∧ n₁ ≤ 10 ^ 37) ∧ (2 ^ 120 < n₁ ∧ n₁ < 2 ^ 121) ∧
    IsFirstKPrimesStrongPseudoprime 20 n₁ ∧ ¬ IsStrongProbablePrime n₁ 73 ∧
    73 ^ (n₁ - 1) ≡ 1 [MOD n₁] ∧
    IsK2Number n₂ p₂ ∧ (10 ^ 36 < n₂ ∧ n₂ ≤ 10 ^ 37) ∧ (2 ^ 122 < n₂ ∧ n₂ < 2 ^ 123) ∧
    IsFirstKPrimesStrongPseudoprime 20 n₂ ∧ ¬ IsStrongProbablePrime n₂ 73 ∧
    73 ^ (n₂ - 1) ≡ 1 [MOD n₂] ∧
    psi 20 ≤ n₁ ∧ psi 20 < 2 ^ 121 ∧ (∀ k ≤ 20, psi k ≤ n₁) :=
  ⟨n₁_isK2, n₁_in_band, n₁_bit_bounds, n₁_spsp_20, n₁_fails_73, n₁_fermat_73,
   n₂_isK2, n₂_in_band, n₂_bit_bounds, n₂_spsp_20, n₂_fails_73, n₂_fermat_73,
   psi_20_le_n₁, lt_of_le_of_lt psi_20_le_n₁ n₁_bit_bounds.2, psi_le_n₁_of_le_20⟩

end SpspPsi20

end
