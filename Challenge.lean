module

public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Data.Nat.Prime.Nth
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.ZMod.Units
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
public import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# Palomar Challenge: Two 37-Digit 20-Base Strong Pseudoprimes (`ψ_20 ≤ n₁ < 2^121`), Order Criteria, and Exact Sieve Laws

Self-contained Lean 4 + Mathlib statements over `ℕ`, `ℤ`, `ℚ`, and `ZMod`
(zero `sorry` in `Solution`, zero `native_decide`, standard axioms only):

1. **Theorem 1 (`main_two_witnesses`, `psi_20_le_n₁`):** Two explicit 37-digit
   Zhang `K2` semiprimes `n₁ = p₁(2p₁ - 1) = 2481162833436289154832260656117034821`
   (121 bits) and `n₂ = p₂(2p₂ - 1) = 5959902256870799858089729225626992341`
   (123 bits) each have Pratt-certified prime factors `p_i` and `2p_i - 1`, pass the
   Miller-Rabin strong probable prime test for all 20 prime bases `Nat.nth Nat.Prime 0..19`
   (`2, 3, ..., 71`), fail the strong test at the 21st prime `73` while passing the Fermat
   test at `73`, and unconditionally establish `ψ_20 ≤ n₁ < 2^121` and `∀ k ≤ 20, ψ_k ≤ n₁`.
2. **Theorem 2 (`k2_fermat_and_sprp_criteria`):** For any odd prime `p` with `n = p(2p - 1)`
   in `K2` and `gcd(b, n) = 1`, Fermat pseudoprimality holds iff `(b / (2p - 1)) = 1`, and
   strong pseudoprimality holds iff `v_2(ord_p b) = v_2(ord_{2p-1} b)` iff
   `twoPowLevel (2p - 1) b = twoPowLevel p b + 1`.
3. **Proposition 3 (`k2_strongLiar_share_and_base2_cap`):** Exact strong-liar fraction
   `strongLiarCount n / φ(n) = (1 + 2 * 4^(-v_2(p - 1))) / 6`, base-2 exclusion when
   `p ≡ 3 (mod 4)`, and the sharp cap `≤ 3/16` (attained at `v_2(p - 1) = 2`) whenever `n`
   passes base `2`.
4. **Proposition 4 (`sieve_admissible_and_wheel`):** Exact odd-prime sieve admissible count
   `A(b) = (b - 1)/2` (`b ≡ 3 mod 4`) or `(b - 3)/2` (`b ≡ 1 mod 4`), and the exact
   10-prime first-wheel count `10,135,125` classes modulo `401,120,980,260`.
5. **Theorem 5 (`k2_jacobsthal_and_cells`):** Exact Jacobsthal character sum
   `∑_{x ∈ ZMod b} χ(x) χ(2x - 1) = -(2/b)` and exact `b mod 8` cell counts `4 N_{-+}` and
   `4 N_{++}`.
6. **Proposition 6 (`k_gen_legendre_of_ratio`):** General `K_{a/b}` 2-adic Legendre
   obstruction for any odd primes `p, q` with `b(q - 1) = a(p - 1)` and `gcd(a, b) = 1`.
7. **Sanity witness (`nth_prime_20`):** `Nat.nth Nat.Prime 20 = 73`, grounding the 0-indexed
   `Nat.nth Nat.Prime` convention.
-/

@[expose] public section

namespace SpspPsi20Challenge

open scoped BigOperators

/-- An odd integer `n ≥ 3` is a **strong probable prime** to base `a` when,
writing `n - 1 = 2^s * d` with `d` odd, either `a^d ≡ 1 [MOD n]` or
`a^(2^r * d) ≡ n - 1 [MOD n]` for some `r < s`. -/
def IsStrongProbablePrime (n a : ℕ) : Prop :=
  Odd n ∧ 3 ≤ n ∧
    ∃ s d : ℕ, Odd d ∧ n - 1 = 2 ^ s * d ∧
      (a ^ d ≡ 1 [MOD n] ∨ ∃ r < s, a ^ (2 ^ r * d) ≡ n - 1 [MOD n])

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

/-- For an odd prime `r` and `b` coprime to `r`, `twoPowLevel r b` is the largest
`j ≤ padicValNat 2 (r - 1)` such that `b ^ ((r - 1) / 2 ^ j) ≡ 1 [MOD r]`. -/
def twoPowLevel (r b : ℕ) : ℕ :=
  ((Finset.range (padicValNat 2 (r - 1) + 1)).filter
    (fun j => b ^ ((r - 1) / 2 ^ j) ≡ 1 [MOD r])).sup id

open Classical in
/-- The finite set of strong-liar bases `b ∈ {0, …, n - 1}` coprime to `n`. -/
noncomputable def strongLiarFinset (n : ℕ) : Finset ℕ :=
  (Finset.range n).filter (fun b => Nat.Coprime b n ∧ IsStrongProbablePrime n b)

/-- Number of units `b ∈ (ℤ/nℤ)ˣ` (represented in `{0, …, n - 1}`) for which `n` passes
the strong probable prime test. -/
noncomputable def strongLiarCount (n : ℕ) : ℕ :=
  (strongLiarFinset n).card

/-- First `K2` prime factor `p₁`. -/
def p₁ : ℕ := 1113813905784150541

/-- Companion prime `q₁ = 2 * p₁ - 1 = 2227627811568301081`. -/
def q₁ : ℕ := 2 * p₁ - 1

/-- First 37-digit 20-base strong pseudoprime `n₁ = p₁ * q₁ = 2481162833436289154832260656117034821`. -/
def n₁ : ℕ := p₁ * q₁

/-- Second `K2` prime factor `p₂`. -/
def p₂ : ℕ := 1726253494836549181

/-- Companion prime `q₂ = 2 * p₂ - 1 = 3452506989673098361`. -/
def q₂ : ℕ := 2 * p₂ - 1

/-- Second 37-digit 20-base strong pseudoprime `n₂ = p₂ * q₂ = 5959902256870799858089729225626992341`. -/
def n₂ : ℕ := p₂ * q₂

/-- Theorem 1: both 37-digit `K2` witnesses `n₁` (121 bits) and `n₂` (123 bits)
pass the first 20 prime bases, fail the strong test at base `73` while passing Fermat at `73`,
and yield `ψ_20 ≤ n₁ < 2^121` and `∀ k ≤ 20, ψ_k ≤ n₁`. -/
theorem main_two_witnesses :
    IsK2Number n₁ p₁ ∧ (10 ^ 36 < n₁ ∧ n₁ ≤ 10 ^ 37) ∧ (2 ^ 120 < n₁ ∧ n₁ < 2 ^ 121) ∧
    IsFirstKPrimesStrongPseudoprime 20 n₁ ∧ ¬ IsStrongProbablePrime n₁ 73 ∧
    73 ^ (n₁ - 1) ≡ 1 [MOD n₁] ∧
    IsK2Number n₂ p₂ ∧ (10 ^ 36 < n₂ ∧ n₂ ≤ 10 ^ 37) ∧ (2 ^ 122 < n₂ ∧ n₂ < 2 ^ 123) ∧
    IsFirstKPrimesStrongPseudoprime 20 n₂ ∧ ¬ IsStrongProbablePrime n₂ 73 ∧
    73 ^ (n₂ - 1) ≡ 1 [MOD n₂] ∧
    psi 20 ≤ n₁ ∧ psi 20 < 2 ^ 121 ∧ (∀ k ≤ 20, psi k ≤ n₁) := by
  sorry

/-- Direct headline upper bound `ψ_20 ≤ 2481162833436289154832260656117034821`. -/
theorem psi_20_le_n₁ : psi 20 ≤ n₁ := by
  sorry

/-- Theorem 2: Fermat Legendre criterion and Miller-Rabin 2-adic order/level criteria
for any odd prime `p` with `n = p(2p - 1)` in `K2` and `gcd(b, n) = 1`. -/
theorem k2_fermat_and_sprp_criteria {n p b : ℕ} (hk2 : IsK2Number n p) (hp_odd : Odd p)
    [Fact (Nat.Prime (2 * p - 1))] (hcop : Nat.Coprime b n) :
    (b ^ (n - 1) ≡ 1 [MOD n] ↔ legendreSym (2 * p - 1) (b : ℤ) = 1) ∧
    (IsStrongProbablePrime n b ↔
      padicValNat 2 (orderOf (b : ZMod p)) =
        padicValNat 2 (orderOf (b : ZMod (2 * p - 1)))) ∧
    (IsStrongProbablePrime n b ↔ twoPowLevel (2 * p - 1) b = twoPowLevel p b + 1) := by
  sorry

/-- Proposition 3: exact strong-liar fraction `(1 + 2 * 4^(-e)) / 6`, base-2 exclusion at
`p % 4 = 3`, congruence constraints and `≤ 3/16` cap when passing base `2`, and equality
`3/16` at `e = 2`. -/
theorem k2_strongLiar_share_and_base2_cap {n p : ℕ} (hk2 : IsK2Number n p) (hp_odd : Odd p) :
    ((strongLiarCount n : ℚ) / (Nat.totient n : ℚ) =
      (1 + 2 * (4 : ℚ) ^ (-(padicValNat 2 (p - 1) : ℤ))) / 6) ∧
    (p % 4 = 3 → (strongLiarCount n : ℚ) / (Nat.totient n : ℚ) = 1 / 4 ∧
      ¬ IsStrongProbablePrime n 2) ∧
    (IsStrongProbablePrime n 2 →
      p % 4 = 1 ∧ (2 * p - 1) % 8 = 1 ∧ n % 4 = 1 ∧
        (strongLiarCount n : ℚ) / (Nat.totient n : ℚ) ≤ 3 / 16) ∧
    (padicValNat 2 (p - 1) = 2 →
      (strongLiarCount n : ℚ) / (Nat.totient n : ℚ) = 3 / 16) := by
  sorry

/-- Proposition 4: exact odd-prime admissible residue count `A(b)` together with the
exact first-wheel modulus `401,120,980,260` and admissible class count `10,135,125`. -/
theorem sieve_admissible_and_wheel {b : ℕ} [Fact b.Prime] (hb_odd : Odd b) :
    (Finset.univ.filter
      (fun x : ZMod b => x ≠ 0 ∧ quadraticChar (ZMod b) (2 * x - 1) = 1)).card =
      (if b % 4 = 3 then (b - 1) / 2 else (b - 3) / 2) ∧
    4 * ([3, 5, 7, 11, 13, 17, 19, 23, 29, 31] : List ℕ).prod = 401120980260 ∧
    (([3, 5, 7, 11, 13, 17, 19, 23, 29, 31] : List ℕ).map
      (fun q => if q % 4 = 3 then (q - 1) / 2 else (q - 3) / 2)).prod = 10135125 := by
  sorry

/-- Theorem 5: exact Jacobsthal correlation sum `-(2/b)` and exact `b mod 8`
wheel-admissible cell identities `4 N_{-+}` and `4 N_{++}`. -/
theorem k2_jacobsthal_and_cells {b : ℕ} [Fact b.Prime] (hb_odd : Odd b) :
    ((∑ x : ZMod b, quadraticChar (ZMod b) x * quadraticChar (ZMod b) (2 * x - 1)) =
      -legendreSym b 2) ∧
    (4 * ((Finset.univ.filter
        (fun x : ZMod b =>
          quadraticChar (ZMod b) x = -1 ∧ quadraticChar (ZMod b) (2 * x - 1) = 1)).card : ℤ) =
      (b : ℤ) - 2 - legendreSym b (-1) + 2 * legendreSym b 2) ∧
    (4 * ((Finset.univ.filter
        (fun x : ZMod b =>
          quadraticChar (ZMod b) x = 1 ∧ quadraticChar (ZMod b) (2 * x - 1) = 1)).card : ℤ) =
      (b : ℤ) - 2 - legendreSym b (-1) - 2 * legendreSym b 2) := by
  sorry

/-- Proposition 6: general ratio `b(q - 1) = a(p - 1)` 2-adic Legendre obstruction. -/
theorem k_gen_legendre_of_ratio {p q a b n c : ℕ}
    [Fact p.Prime] [Fact q.Prime]
    (hp_odd : Odd p) (hq_odd : Odd q)
    (hb : 0 < b) (hcop_ab : Nat.Coprime a b)
    (hrel : b * (q - 1) = a * (p - 1))
    (hn_eq : n = p * q) (hcop_cn : Nat.Coprime c n)
    (hsprp : IsStrongProbablePrime n c) :
    (padicValNat 2 a = padicValNat 2 b →
      legendreSym p (c : ℤ) = legendreSym q (c : ℤ)) ∧
    (padicValNat 2 b < padicValNat 2 a →
      legendreSym q (c : ℤ) = 1) ∧
    (padicValNat 2 a < padicValNat 2 b →
      legendreSym p (c : ℤ) = 1) := by
  sorry

/-- Grounding witness: the 21st prime (0-indexed 20) is `73`. -/
theorem nth_prime_20 : Nat.nth Nat.Prime 20 = 73 := by
  sorry

end SpspPsi20Challenge

end
