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
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.ZMod.Units
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import SpspPsi20

/-!
# Palomar Solution: Two 37-Digit 20-Base Strong Pseudoprimes (`ψ_20 ≤ n₁ < 2^121`), Order Criteria, and Exact Sieve Laws
-/

@[expose] public section

namespace SpspPsi20Challenge

open scoped BigOperators

def IsStrongProbablePrime (n a : ℕ) : Prop :=
  Odd n ∧ 3 ≤ n ∧
    ∃ s d : ℕ, Odd d ∧ n - 1 = 2 ^ s * d ∧
      (a ^ d ≡ 1 [MOD n] ∨ ∃ r < s, a ^ (2 ^ r * d) ≡ n - 1 [MOD n])

def IsFirstKPrimesStrongPseudoprime (k n : ℕ) : Prop :=
  Odd n ∧ 3 ≤ n ∧ ¬ Nat.Prime n ∧
    ∀ i < k, IsStrongProbablePrime n (Nat.nth Nat.Prime i)

noncomputable def psi (k : ℕ) : ℕ :=
  sInf { n : ℕ | IsFirstKPrimesStrongPseudoprime k n }

def IsK2Number (n p : ℕ) : Prop :=
  Nat.Prime p ∧ Nat.Prime (2 * p - 1) ∧ n = p * (2 * p - 1)

def twoPowLevel (r b : ℕ) : ℕ :=
  ((Finset.range (padicValNat 2 (r - 1) + 1)).filter
    (fun j => b ^ ((r - 1) / 2 ^ j) ≡ 1 [MOD r])).sup id

open Classical in
noncomputable def strongLiarFinset (n : ℕ) : Finset ℕ :=
  (Finset.range n).filter (fun b => Nat.Coprime b n ∧ IsStrongProbablePrime n b)

noncomputable def strongLiarCount (n : ℕ) : ℕ :=
  (strongLiarFinset n).card

def p₁ : ℕ := 1113813905784150541
def q₁ : ℕ := 2 * p₁ - 1
def n₁ : ℕ := p₁ * q₁
def p₂ : ℕ := 1726253494836549181
def q₂ : ℕ := 2 * p₂ - 1
def n₂ : ℕ := p₂ * q₂

private theorem p₁_eq_lib : p₁ = SpspPsi20.p₁ := rfl
private theorem n₁_eq_lib : n₁ = SpspPsi20.n₁ := rfl
private theorem p₂_eq_lib : p₂ = SpspPsi20.p₂ := rfl
private theorem n₂_eq_lib : n₂ = SpspPsi20.n₂ := rfl

theorem main_two_witnesses :
    IsK2Number n₁ p₁ ∧ (10 ^ 36 < n₁ ∧ n₁ ≤ 10 ^ 37) ∧ (2 ^ 120 < n₁ ∧ n₁ < 2 ^ 121) ∧
    IsFirstKPrimesStrongPseudoprime 20 n₁ ∧ ¬ IsStrongProbablePrime n₁ 73 ∧
    73 ^ (n₁ - 1) ≡ 1 [MOD n₁] ∧
    IsK2Number n₂ p₂ ∧ (10 ^ 36 < n₂ ∧ n₂ ≤ 10 ^ 37) ∧ (2 ^ 122 < n₂ ∧ n₂ < 2 ^ 123) ∧
    IsFirstKPrimesStrongPseudoprime 20 n₂ ∧ ¬ IsStrongProbablePrime n₂ 73 ∧
    73 ^ (n₂ - 1) ≡ 1 [MOD n₂] ∧
    psi 20 ≤ n₁ ∧ psi 20 < 2 ^ 121 ∧ (∀ k ≤ 20, psi k ≤ n₁) := by
  rw [p₁_eq_lib, n₁_eq_lib, p₂_eq_lib, n₂_eq_lib]
  exact SpspPsi20.main_two_witnesses

theorem psi_20_le_n₁ : psi 20 ≤ n₁ := by
  rw [n₁_eq_lib]
  exact SpspPsi20.psi_20_le_n₁

theorem k2_fermat_and_sprp_criteria {n p b : ℕ} (hk2 : IsK2Number n p) (hp_odd : Odd p)
    [Fact (Nat.Prime (2 * p - 1))] (hcop : Nat.Coprime b n) :
    (b ^ (n - 1) ≡ 1 [MOD n] ↔ legendreSym (2 * p - 1) (b : ℤ) = 1) ∧
    (IsStrongProbablePrime n b ↔
      padicValNat 2 (orderOf (b : ZMod p)) =
        padicValNat 2 (orderOf (b : ZMod (2 * p - 1)))) ∧
    (IsStrongProbablePrime n b ↔ twoPowLevel (2 * p - 1) b = twoPowLevel p b + 1) :=
  SpspPsi20.k2_fermat_and_sprp_criteria hk2 hp_odd hcop

theorem k2_strongLiar_share_and_base2_cap {n p : ℕ} (hk2 : IsK2Number n p) (hp_odd : Odd p) :
    ((strongLiarCount n : ℚ) / (Nat.totient n : ℚ) =
      (1 + 2 * (4 : ℚ) ^ (-(padicValNat 2 (p - 1) : ℤ))) / 6) ∧
    (p % 4 = 3 → (strongLiarCount n : ℚ) / (Nat.totient n : ℚ) = 1 / 4 ∧
      ¬ IsStrongProbablePrime n 2) ∧
    (IsStrongProbablePrime n 2 →
      p % 4 = 1 ∧ (2 * p - 1) % 8 = 1 ∧ n % 4 = 1 ∧
        (strongLiarCount n : ℚ) / (Nat.totient n : ℚ) ≤ 3 / 16) ∧
    (padicValNat 2 (p - 1) = 2 →
      (strongLiarCount n : ℚ) / (Nat.totient n : ℚ) = 3 / 16) :=
  SpspPsi20.k2_strongLiar_share_and_base2_cap hk2 hp_odd

theorem sieve_admissible_and_wheel {b : ℕ} [Fact b.Prime] (hb_odd : Odd b) :
    (Finset.univ.filter
      (fun x : ZMod b => x ≠ 0 ∧ quadraticChar (ZMod b) (2 * x - 1) = 1)).card =
      (if b % 4 = 3 then (b - 1) / 2 else (b - 3) / 2) ∧
    4 * ([3, 5, 7, 11, 13, 17, 19, 23, 29, 31] : List ℕ).prod = 401120980260 ∧
    (([3, 5, 7, 11, 13, 17, 19, 23, 29, 31] : List ℕ).map
      (fun q => if q % 4 = 3 then (q - 1) / 2 else (q - 3) / 2)).prod = 10135125 :=
  SpspPsi20.sieve_admissible_and_wheel hb_odd

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
      (b : ℤ) - 2 - legendreSym b (-1) - 2 * legendreSym b 2) :=
  SpspPsi20.k2_jacobsthal_and_cells hb_odd

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
      legendreSym p (c : ℤ) = 1) :=
  SpspPsi20.k_gen_legendre_of_ratio hp_odd hq_odd hb hcop_ab hrel hn_eq hcop_cn hsprp

theorem nth_prime_20 : Nat.nth Nat.Prime 20 = 73 :=
  SpspPsi20.nth_prime_20

end SpspPsi20Challenge

end
