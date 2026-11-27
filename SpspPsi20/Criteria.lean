/-
Copyright (c) 2026 Tyler B. Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tyler B. Hughes
-/
module

public import SpspPsi20.Defs
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.ZMod.Units
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.RingTheory.IntegralDomain

import Mathlib.Tactic

/-!
# Algebraic Criteria, Liar Densities, and Sieve Laws for `K2` and `K_{a/b}` Forms

Complete Lean 4 formalization of the algebraic theory in `hughes-spsp-psi20.tex`:

1. **2-power residue levels and semiprime 2-adic order equality**:
   - Exact definition `twoPowLevel r b` (`j_r(b)` in the paper), proved to be the largest
     `j ≤ padicValNat 2 (r - 1)` with `b ^ ((r - 1) / 2 ^ j) ≡ 1 [MOD r]`, and proved to
     satisfy `twoPowLevel r b + padicValNat 2 (orderOf (b : ZMod r)) = padicValNat 2 (r - 1)`.
   - General semiprime equal-2-adic-order theorem (`semiprime_padicValNat_orderOf_eq_of_sprp`,
     Jaeschke's Proposition 1 forward direction).
2. **Theorem 2 (`thm:k2-criterion`)**:
   - `k2_pred_eq`, `k2_padicValNat_pred`, `k2_two_adic_decomp` (Part 1).
   - `k2_fermat_iff_euler`, `k2_fermat_iff_legendre` (Part 2).
   - `k2_sprp_iff_two_adic_order`, `k2_sprp_iff_level` (Part 3).
3. **Corollary 3 (`cor:k2-liars`)**:
   - Exact strong-liar count `strongLiarCount n` satisfying
     `6 * 4 ^ (padicValNat 2 (p - 1)) * strongLiarCount n =
       (4 ^ (padicValNat 2 (p - 1)) + 2) * n.totient`
     and exact rational fraction `(1 + 2 * 4 ^ (-e)) / 6` (`1/4` at `e = 1`, `3/16` at `e = 2`)
     (Part 1).
   - Base-2 obstruction `k2_not_sprp_two_of_mod_four_eq_three`, residue consequences
     `k2_mod_of_sprp_two`, and liar-density cap `≤ 3 / 16` (Part 2).
4. **Lemma 4 (`lem:k-gen`)**:
   - Parameterization `exists_k_gen_param` and general 3-case quadratic-residue criterion
     `k_gen_legendre_of_sprp` / `k_gen_legendre_of_ratio` for `K_{a/b}` semiprimes.
5. **Sieve Admissible-Residue Count and Exact Jacobsthal `b mod 8` Cell Split**:
   - `sieve_admissible_card` / `sieve_admissible_nat_card`: exact admissible residue count
     `(b - 1) / 2` (`b % 4 = 3`) vs `(b - 3) / 2` (`b % 4 = 1`).
   - `jacobsthal_sum_two_mul_sq_sub` and `k2_quadratic_cell_counts`: exact character sum
     `∑ x : ZMod b, χ(x) χ(2x - 1) = -legendreSym b 2` and exact `(-,+)` / `(+,+)` cell counts
     explaining the four-branch `b mod 8` survival law.
-/

@[expose] public section

namespace SpspPsi20

open scoped BigOperators

/-! ## 1. 2-Adic Decomposition and Order Helpers -/

/-- Every positive integer `m` decomposes as `2 ^ padicValNat 2 m * u` with `u` odd. -/
theorem exists_eq_two_pow_padicValNat_mul_odd {m : ℕ} (hm : 0 < m) :
    ∃ u : ℕ, Odd u ∧ m = 2 ^ padicValNat 2 m * u := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set t := padicValNat 2 m
  have hdvd : 2 ^ t ∣ m := pow_padicValNat_dvd
  refine ⟨m / 2 ^ t, ?_, (Nat.mul_div_cancel' hdvd).symm⟩
  by_contra hnot_odd
  have heven : 2 ∣ m / 2 ^ t := by
    rw [Nat.not_odd_iff_even] at hnot_odd
    exact even_iff_two_dvd.mp hnot_odd
  rcases heven with ⟨k, hk⟩
  have hdvd_succ : 2 ^ (t + 1) ∣ m := by
    refine ⟨k, ?_⟩
    have hm_eq : m = 2 ^ t * (m / 2 ^ t) := (Nat.mul_div_cancel' hdvd).symm
    rw [hm_eq, hk, pow_succ]
    ring
  have hle : t + 1 ≤ t := (padicValNat_dvd_iff_le (by omega : m ≠ 0)).mp hdvd_succ
  omega

/-- If `m = 2 ^ t * u` with `u` odd, then `padicValNat 2 m = t`. -/
theorem padicValNat_two_pow_mul_odd {m t u : ℕ} (hu : Odd u) (hm : m = 2 ^ t * u) :
    padicValNat 2 m = t := by
  have hu_pos : 0 < u := by rcases hu with ⟨k, rfl⟩; omega
  have hm_pos : 0 < m := by
    rw [hm]
    exact Nat.mul_pos (Nat.pos_of_ne_zero (by positivity)) hu_pos
  obtain ⟨u', hu'_odd, hm'⟩ := exists_eq_two_pow_padicValNat_mul_odd hm_pos
  exact (odd_two_pow_mul_unique hu'_odd hu (hm'.symm.trans hm)).1

private theorem odd_dvd_of_dvd_two_pow_mul {u k d : ℕ} (hu : Odd u) (hdvd : u ∣ 2 ^ k * d) :
    u ∣ d := by
  have hcop : Nat.Coprime u (2 ^ k) := (Nat.coprime_two_right.mpr hu).pow_right k
  exact hcop.dvd_of_dvd_mul_left hdvd

private theorem two_pow_le_of_dvd_two_pow_mul_odd {t k d : ℕ} (hd : Odd d)
    (hdvd : 2 ^ t ∣ 2 ^ k * d) : t ≤ k := by
  have hcop : Nat.Coprime (2 ^ t) d := (Nat.coprime_two_left.mpr hd).pow_left t
  have hpow : 2 ^ t ∣ 2 ^ k := hcop.dvd_of_dvd_mul_right hdvd
  exact (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).mp hpow

private theorem zmod_natCast_ne_zero_of_coprime {r b : ℕ} (hr : Nat.Prime r)
    (hcop : Nat.Coprime b r) : (b : ZMod r) ≠ 0 := by
  intro hz
  have hdvd : r ∣ b := (ZMod.natCast_eq_zero_iff b r).mp hz
  exact hr.not_dvd_one (hcop.gcd_eq_one ▸ Nat.dvd_gcd hdvd (dvd_refl r))

private theorem orderOf_zmod_dvd_pred {r b : ℕ} (hr : Nat.Prime r)
    (hcop : Nat.Coprime b r) : orderOf (b : ZMod r) ∣ r - 1 := by
  have : Fact r.Prime := ⟨hr⟩
  have hb0 : (b : ZMod r) ≠ 0 := zmod_natCast_ne_zero_of_coprime hr hcop
  exact orderOf_dvd_iff_pow_eq_one.mpr (ZMod.pow_card_sub_one_eq_one hb0)

private theorem orderOf_zmod_pos {r b : ℕ} (hr : Nat.Prime r)
    (hcop : Nat.Coprime b r) : 0 < orderOf (b : ZMod r) := by
  have hdvd := orderOf_zmod_dvd_pred hr hcop
  have hpos : 0 < r - 1 := by have := hr.two_le; omega
  exact Nat.pos_of_dvd_of_pos hdvd hpos

private theorem zmod_neg_one_ne_one_of_odd_prime {r : ℕ} (hr : Nat.Prime r) (hodd : Odd r) :
    (-1 : ZMod r) ≠ (1 : ZMod r) := by
  have : Fact r.Prime := ⟨hr⟩
  have hchar : ringChar (ZMod r) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    rintro rfl
    rcases hodd with ⟨k, hk⟩
    omega
  exact Ring.neg_one_ne_one_of_char_ne_two hchar

private theorem zmod_modEq_pred_iff_eq_neg_one {n r x : ℕ} (hn : 1 ≤ n) (hdvd : r ∣ n) :
    x ≡ n - 1 [MOD r] ↔ (x : ZMod r) = -1 := by
  rw [← ZMod.natCast_eq_natCast_iff]
  have hcast : ((n - 1 : ℕ) : ZMod r) = -1 := by
    rw [Nat.cast_sub hn, (ZMod.natCast_eq_zero_iff n r).mpr hdvd, zero_sub, Nat.cast_one]
  rw [hcast]

/-! ## 2. 2-Power Residue Levels (`twoPowLevel`) and Order Equivalence -/

/-- For an odd prime `r` and `b` coprime to `r`, `twoPowLevel r b` (`j_r(b)` in the paper)
is the largest `j ≤ padicValNat 2 (r - 1)` such that `b ^ ((r - 1) / 2 ^ j) ≡ 1 [MOD r]`. -/
def twoPowLevel (r b : ℕ) : ℕ :=
  ((Finset.range (padicValNat 2 (r - 1) + 1)).filter
    (fun j => b ^ ((r - 1) / 2 ^ j) ≡ 1 [MOD r])).sup id

/-- `twoPowLevel r b` never exceeds `padicValNat 2 (r - 1)`. -/
theorem twoPowLevel_le (r b : ℕ) : twoPowLevel r b ≤ padicValNat 2 (r - 1) := by
  unfold twoPowLevel
  apply Finset.sup_le
  intro j hj
  rw [Finset.mem_filter, Finset.mem_range] at hj
  exact Nat.lt_succ_iff.mp hj.1

/-- Any `j ≤ padicValNat 2 (r - 1)` satisfying `b ^ ((r - 1) / 2 ^ j) ≡ 1 [MOD r]`
is bounded above by `twoPowLevel r b`. -/
theorem le_twoPowLevel_of_modEq_one {r b j : ℕ} (hj : j ≤ padicValNat 2 (r - 1))
    (hmod : b ^ ((r - 1) / 2 ^ j) ≡ 1 [MOD r]) : j ≤ twoPowLevel r b := by
  unfold twoPowLevel
  have hmem : j ∈ (Finset.range (padicValNat 2 (r - 1) + 1)).filter
      (fun k => b ^ ((r - 1) / 2 ^ k) ≡ 1 [MOD r]) := by
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.lt_succ_of_le hj, hmod⟩
  exact Finset.le_sup (f := id) hmem

/-- `twoPowLevel r b` satisfies the defining congruence `b ^ ((r - 1) / 2 ^ j) ≡ 1 [MOD r]`
whenever `r` is prime and `b` is coprime to `r`. -/
theorem twoPowLevel_modEq_one {r b : ℕ} (hr : Nat.Prime r) (hcop : Nat.Coprime b r) :
    b ^ ((r - 1) / 2 ^ twoPowLevel r b) ≡ 1 [MOD r] := by
  set S := (Finset.range (padicValNat 2 (r - 1) + 1)).filter
    (fun j => b ^ ((r - 1) / 2 ^ j) ≡ 1 [MOD r])
  have h0 : 0 ∈ S := by
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨Nat.succ_pos _, ?_⟩
    simp only [pow_zero, Nat.div_one]
    have : Fact r.Prime := ⟨hr⟩
    rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_pow, Nat.cast_one]
    exact ZMod.pow_card_sub_one_eq_one (zmod_natCast_ne_zero_of_coprime hr hcop)
  have hne : S.Nonempty := ⟨0, h0⟩
  have hsup_mem : S.sup id ∈ S := by
    have heq : S.sup id = S.max' hne := by
      rw [← Finset.sup'_eq_sup hne, Finset.max'_eq_sup']
    rw [heq]
    exact Finset.max'_mem S hne
  exact (Finset.mem_filter.mp hsup_mem).2

/-- For prime `r` and `Nat.Coprime b r`, the 2-adic valuation of `orderOf (b : ZMod r)`
is at most `padicValNat 2 (r - 1)`. -/
theorem padicValNat_orderOf_le {r b : ℕ} (hr : Nat.Prime r) (hcop : Nat.Coprime b r) :
    padicValNat 2 (orderOf (b : ZMod r)) ≤ padicValNat 2 (r - 1) := by
  have hdvd := orderOf_zmod_dvd_pred hr hcop
  have hpos_ord := orderOf_zmod_pos hr hcop
  have hpos_rm1 : 0 < r - 1 := by have := hr.two_le; omega
  obtain ⟨u, _, hu_eq⟩ := exists_eq_two_pow_padicValNat_mul_odd hpos_ord
  obtain ⟨m, hm_odd, hm_eq⟩ := exists_eq_two_pow_padicValNat_mul_odd hpos_rm1
  have h2dvd : 2 ^ padicValNat 2 (orderOf (b : ZMod r)) ∣ 2 ^ padicValNat 2 (r - 1) * m := by
    refine dvd_trans ⟨u, hu_eq⟩ ?_
    rwa [← hm_eq]
  exact two_pow_le_of_dvd_two_pow_mul_odd hm_odd h2dvd

/-- Exact complementary relation `j_r(b) + v_2(ord_r(b)) = v_2(r - 1)` for prime `r`
and `Nat.Coprime b r`. -/
theorem twoPowLevel_add_padicValNat_orderOf {r b : ℕ} (hr : Nat.Prime r)
    (hcop : Nat.Coprime b r) :
    twoPowLevel r b + padicValNat 2 (orderOf (b : ZMod r)) = padicValNat 2 (r - 1) := by
  have hpos_ord := orderOf_zmod_pos hr hcop
  have hpos_rm1 : 0 < r - 1 := by have := hr.two_le; omega
  have hdvd_ord := orderOf_zmod_dvd_pred hr hcop
  obtain ⟨u, hu_odd, hu_eq⟩ := exists_eq_two_pow_padicValNat_mul_odd hpos_ord
  obtain ⟨m, hm_odd, hm_eq⟩ := exists_eq_two_pow_padicValNat_mul_odd hpos_rm1
  set E := padicValNat 2 (r - 1)
  set t := padicValNat 2 (orderOf (b : ZMod r))
  have ht_le : t ≤ E := padicValNat_orderOf_le hr hcop
  have hu_dvd_m : u ∣ m := by
    have hd : u ∣ 2 ^ E * m := dvd_trans ⟨2 ^ t, hu_eq.trans (mul_comm _ _)⟩ (hm_eq ▸ hdvd_ord)
    exact odd_dvd_of_dvd_two_pow_mul hu_odd hd
  have hiff : ∀ j ≤ E, b ^ ((r - 1) / 2 ^ j) ≡ 1 [MOD r] ↔ j ≤ E - t := by
    intro j hj
    have hdiv_eq : (r - 1) / 2 ^ j = 2 ^ (E - j) * m := by
      have hexp : E = j + (E - j) := by omega
      have hrm1 : r - 1 = 2 ^ j * (2 ^ (E - j) * m) := by
        calc
          r - 1 = 2 ^ E * m := hm_eq
          _ = 2 ^ (j + (E - j)) * m := by rw [← hexp]
          _ = 2 ^ j * (2 ^ (E - j) * m) := by rw [pow_add]; ring
      rw [hrm1, Nat.mul_div_cancel_left _ (by positivity)]
    rw [hdiv_eq, ← ZMod.natCast_eq_natCast_iff, Nat.cast_pow, Nat.cast_one,
      ← orderOf_dvd_iff_pow_eq_one, hu_eq]
    constructor
    · intro hd
      have h2 : 2 ^ t ∣ 2 ^ (E - j) * m := dvd_trans ⟨u, rfl⟩ hd
      have htle : t ≤ E - j := two_pow_le_of_dvd_two_pow_mul_odd hm_odd h2
      omega
    · intro hjle
      have hpow : 2 ^ t ∣ 2 ^ (E - j) := pow_dvd_pow 2 (by omega)
      exact mul_dvd_mul hpow hu_dvd_m
  have hge : E - t ≤ twoPowLevel r b :=
    le_twoPowLevel_of_modEq_one (by omega) ((hiff (E - t) (by omega)).mpr le_rfl)
  have hle : twoPowLevel r b ≤ E - t :=
    (hiff (twoPowLevel r b) (twoPowLevel_le r b)).mp (twoPowLevel_modEq_one hr hcop)
  omega

/-- Explicit subtraction form `j_r(b) = v_2(r - 1) - v_2(ord_r(b))`. -/
theorem twoPowLevel_eq_sub {r b : ℕ} (hr : Nat.Prime r) (hcop : Nat.Coprime b r) :
    twoPowLevel r b = padicValNat 2 (r - 1) - padicValNat 2 (orderOf (b : ZMod r)) := by
  have h := twoPowLevel_add_padicValNat_orderOf hr hcop
  omega

/-! ## 3. General Semiprime 2-Adic Order Equality (Jaeschke Proposition 1 Forward Direction) -/

private theorem padicValNat_orderOf_eq_zero_of_pow_odd_eq_one {r c d : ℕ}
    (hd : Odd d) (hpow : (c : ZMod r) ^ d = 1) :
    padicValNat 2 (orderOf (c : ZMod r)) = 0 := by
  have hdvd : orderOf (c : ZMod r) ∣ d := orderOf_dvd_iff_pow_eq_one.mpr hpow
  have hodd_ord : Odd (orderOf (c : ZMod r)) := Odd.of_dvd_nat hd hdvd
  exact padicValNat.eq_zero_of_not_dvd (by rcases hodd_ord with ⟨k, hk⟩; omega)

private theorem padicValNat_orderOf_eq_succ_of_pow_eq_neg_one {r c k d : ℕ}
    (hr : Nat.Prime r) (hr_odd : Odd r) (hd : Odd d)
    (hpow : (c : ZMod r) ^ (2 ^ k * d) = -1) :
    padicValNat 2 (orderOf (c : ZMod r)) = k + 1 := by
  have hsq : (c : ZMod r) ^ (2 ^ (k + 1) * d) = 1 := by
    have hexp : 2 ^ (k + 1) * d = (2 ^ k * d) * 2 := by rw [pow_succ]; ring
    rw [hexp, pow_mul, hpow, neg_one_sq]
  have hdvd : orderOf (c : ZMod r) ∣ 2 ^ (k + 1) * d := orderOf_dvd_iff_pow_eq_one.mpr hsq
  have hndvd : ¬ (orderOf (c : ZMod r) ∣ 2 ^ k * d) := by
    intro hdvd'
    have h1 : (c : ZMod r) ^ (2 ^ k * d) = 1 := orderOf_dvd_iff_pow_eq_one.mp hdvd'
    exact zmod_neg_one_ne_one_of_odd_prime hr hr_odd (hpow.symm.trans h1)
  have hd_pos : 0 < d := by rcases hd with ⟨j, rfl⟩; omega
  have hord_pos : 0 < orderOf (c : ZMod r) :=
    Nat.pos_of_dvd_of_pos hdvd (Nat.mul_pos (by positivity) hd_pos)
  obtain ⟨u, hu_odd, hu_eq⟩ := exists_eq_two_pow_padicValNat_mul_odd hord_pos
  set t := padicValNat 2 (orderOf (c : ZMod r))
  have ht_le : t ≤ k + 1 :=
    two_pow_le_of_dvd_two_pow_mul_odd hd (dvd_trans ⟨u, hu_eq⟩ hdvd)
  have hu_dvd : u ∣ d :=
    odd_dvd_of_dvd_two_pow_mul hu_odd (dvd_trans ⟨2 ^ t, hu_eq.trans (mul_comm _ _)⟩ hdvd)
  by_contra hne
  have ht_le_k : t ≤ k := by omega
  apply hndvd
  rw [hu_eq]
  exact mul_dvd_mul (pow_dvd_pow 2 ht_le_k) hu_dvd

/-- **Jaeschke's Proposition 1 (forward direction for semiprimes)**:
If `n = p * q` with odd primes `p, q` passes the strong probable prime test to base `c`,
then the 2-adic valuations of the multiplicative orders of `c` modulo `p` and modulo `q`
are equal. -/
theorem semiprime_padicValNat_orderOf_eq_of_sprp {p q n c : ℕ}
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hp_odd : Odd p) (hq_odd : Odd q)
    (hn : n = p * q) (hsprp : IsStrongProbablePrime n c) :
    padicValNat 2 (orderOf (c : ZMod p)) = padicValNat 2 (orderOf (c : ZMod q)) := by
  rcases hsprp with ⟨_, h3, _, d, hd_odd, _, hbase | ⟨k, _, hneg⟩⟩
  · have hp_dvd : p ∣ n := ⟨q, hn⟩
    have hq_dvd : q ∣ n := ⟨p, by rw [hn, mul_comm]⟩
    have hcp : (c : ZMod p) ^ d = 1 := by
      simpa [Nat.cast_pow, Nat.cast_one] using
        (ZMod.natCast_eq_natCast_iff (c ^ d) 1 p).mpr (hbase.of_dvd hp_dvd)
    have hcq : (c : ZMod q) ^ d = 1 := by
      simpa [Nat.cast_pow, Nat.cast_one] using
        (ZMod.natCast_eq_natCast_iff (c ^ d) 1 q).mpr (hbase.of_dvd hq_dvd)
    rw [padicValNat_orderOf_eq_zero_of_pow_odd_eq_one hd_odd hcp,
      padicValNat_orderOf_eq_zero_of_pow_odd_eq_one hd_odd hcq]
  · have hp_dvd : p ∣ n := ⟨q, hn⟩
    have hq_dvd : q ∣ n := ⟨p, by rw [hn, mul_comm]⟩
    have hcp : (c : ZMod p) ^ (2 ^ k * d) = -1 := by
      have hm := (zmod_modEq_pred_iff_eq_neg_one (by omega : 1 ≤ n) hp_dvd).mp
        (hneg.of_dvd hp_dvd)
      simpa [Nat.cast_pow] using hm
    have hcq : (c : ZMod q) ^ (2 ^ k * d) = -1 := by
      have hm := (zmod_modEq_pred_iff_eq_neg_one (by omega : 1 ≤ n) hq_dvd).mp
        (hneg.of_dvd hq_dvd)
      simpa [Nat.cast_pow] using hm
    rw [padicValNat_orderOf_eq_succ_of_pow_eq_neg_one hp hp_odd hd_odd hcp,
      padicValNat_orderOf_eq_succ_of_pow_eq_neg_one hq hq_odd hd_odd hcq]

/-! ## 4. Theorem 2 (`thm:k2-criterion`): Algebraic Criterion for `K2` Numbers -/

/-- The prime factors `p` and `2 * p - 1` of any `K2` number are coprime. -/
theorem k2_coprime_factors {n p : ℕ} (hk2 : IsK2Number n p) :
    Nat.Coprime p (2 * p - 1) := by
  have hp2 : 2 ≤ p := hk2.1.two_le
  refine Nat.coprime_of_dvd' fun r _ hp_dvd hq_dvd => ?_
  have h2p : r ∣ 2 * p := dvd_mul_of_dvd_right hp_dvd 2
  have h1 : 2 * p - (2 * p - 1) = 1 := by omega
  rw [← h1]
  exact Nat.dvd_sub h2p hq_dvd

/-- **Theorem 2(1), algebraic factorization**: For any `K2` number `n = p(2p - 1)`,
`n - 1 = (2p + 1)(p - 1)`. -/
theorem k2_pred_eq {n p : ℕ} (hk2 : IsK2Number n p) :
    n - 1 = (2 * p + 1) * (p - 1) := by
  rcases hk2 with ⟨hp, _, rfl⟩
  obtain ⟨k, rfl⟩ : ∃ k, p = k + 2 := ⟨p - 2, by have := hp.two_le; omega⟩
  have h1 : 2 * (k + 2) - 1 = 2 * k + 3 := by omega
  have h2 : (k + 2) - 1 = k + 1 := by omega
  have h3 : (k + 2) * (2 * k + 3) = (2 * (k + 2) + 1) * (k + 1) + 1 := by ring
  rw [h1, h2, h3]
  omega

/-- **Theorem 2(1), explicit 2-adic decomposition**: If `IsK2Number n p` and `p - 1 = 2 ^ e * m`
with `m` odd, then `n - 1 = 2 ^ e * ((2p + 1) * m)` with `(2p + 1) * m` odd and
`(2p - 1) - 1 = 2 ^ (e + 1) * m`. -/
theorem k2_two_adic_decomp {n p e m : ℕ} (hk2 : IsK2Number n p) (hm : Odd m)
    (hp_decomp : p - 1 = 2 ^ e * m) :
    n - 1 = 2 ^ e * ((2 * p + 1) * m) ∧
      Odd ((2 * p + 1) * m) ∧
      (2 * p - 1) - 1 = 2 ^ (e + 1) * m := by
  refine ⟨?_, ?_, ?_⟩
  · rw [k2_pred_eq hk2, hp_decomp]
    ring
  · exact Odd.mul ⟨p, rfl⟩ hm
  · have hp2 : 2 ≤ p := hk2.1.two_le
    have hq : (2 * p - 1) - 1 = 2 * (p - 1) := by omega
    rw [hq, hp_decomp, pow_succ']
    ring

/-- **Theorem 2(1), 2-adic valuation identity**: For any `K2` number `n = p(2p - 1)`,
`v_2(n - 1) = v_2(p - 1)` and `v_2((2p - 1) - 1) = v_2(p - 1) + 1`. -/
theorem k2_padicValNat_pred {n p : ℕ} (hk2 : IsK2Number n p) :
    padicValNat 2 (n - 1) = padicValNat 2 (p - 1) ∧
      padicValNat 2 ((2 * p - 1) - 1) = padicValNat 2 (p - 1) + 1 := by
  have hp_pos : 0 < p - 1 := by have := hk2.1.two_le; omega
  obtain ⟨m, hm_odd, hm_eq⟩ := exists_eq_two_pow_padicValNat_mul_odd hp_pos
  obtain ⟨hn_eq, hd_odd, hq_eq⟩ := k2_two_adic_decomp hk2 hm_odd hm_eq
  exact ⟨padicValNat_two_pow_mul_odd hd_odd hn_eq,
    padicValNat_two_pow_mul_odd hm_odd hq_eq⟩

/-- **Theorem 2(2), Euler-criterion form**: For `IsK2Number n p` and `Nat.Coprime b n`,
`b ^ (n - 1) ≡ 1 [MOD n]` iff `b ^ (p - 1) ≡ 1 [MOD (2p - 1)]`
(note `((2p - 1) - 1) / 2 = p - 1`). -/
theorem k2_fermat_iff_euler {n p b : ℕ} (hk2 : IsK2Number n p)
    (hcop : Nat.Coprime b n) :
    b ^ (n - 1) ≡ 1 [MOD n] ↔ b ^ (p - 1) ≡ 1 [MOD (2 * p - 1)] := by
  have hcop_pq : Nat.Coprime p (2 * p - 1) := k2_coprime_factors hk2
  rcases hk2 with ⟨hp, hq, rfl⟩
  have hcop_bp : Nat.Coprime b p := hcop.coprime_mul_right_right
  have hcop_bq : Nat.Coprime b (2 * p - 1) := hcop.coprime_mul_left_right
  rw [← Nat.modEq_and_modEq_iff_modEq_mul hcop_pq]
  have hp_fermat : b ^ (p * (2 * p - 1) - 1) ≡ 1 [MOD p] := by
    have : Fact p.Prime := ⟨hp⟩
    rw [k2_pred_eq ⟨hp, hq, rfl⟩, mul_comm, pow_mul, ← ZMod.natCast_eq_natCast_iff,
      Nat.cast_pow, Nat.cast_pow, Nat.cast_one,
      ZMod.pow_card_sub_one_eq_one (zmod_natCast_ne_zero_of_coprime hp hcop_bp), one_pow]
  rw [and_iff_right hp_fermat, k2_pred_eq ⟨hp, hq, rfl⟩,
    ← ZMod.natCast_eq_natCast_iff, ← ZMod.natCast_eq_natCast_iff,
    Nat.cast_pow, Nat.cast_pow, Nat.cast_one,
    ← orderOf_dvd_iff_pow_eq_one, ← orderOf_dvd_iff_pow_eq_one]
  have hord_q : orderOf (b : ZMod (2 * p - 1)) ∣ 2 * (p - 1) := by
    have hqm1 : (2 * p - 1) - 1 = 2 * (p - 1) := by have := hp.two_le; omega
    rw [← hqm1]
    exact orderOf_zmod_dvd_pred hq hcop_bq
  have hgcd : Nat.gcd ((2 * p + 1) * (p - 1)) (2 * (p - 1)) = p - 1 := by
    rw [Nat.gcd_mul_right]
    have hcop2 : Nat.Coprime (2 * p + 1) 2 := Nat.coprime_two_right.mpr ⟨p, rfl⟩
    rw [hcop2.gcd_eq_one, one_mul]
  constructor
  · intro hdvd
    rw [← hgcd]
    exact Nat.dvd_gcd hdvd hord_q
  · intro hdvd
    exact dvd_mul_of_dvd_right hdvd (2 * p + 1)

/-- **Theorem 2(2), Legendre-symbol form**: For `IsK2Number n p` and `Nat.Coprime b n`,
`n` is a Fermat probable prime to base `b` iff `legendreSym (2p - 1) b = 1`. -/
theorem k2_fermat_iff_legendre {n p b : ℕ} (hk2 : IsK2Number n p)
    [Fact (Nat.Prime (2 * p - 1))] (hcop : Nat.Coprime b n) :
    b ^ (n - 1) ≡ 1 [MOD n] ↔ legendreSym (2 * p - 1) (b : ℤ) = 1 := by
  rw [k2_fermat_iff_euler hk2 hcop]
  rcases hk2 with ⟨hp, hq, rfl⟩
  have hcop_bq : Nat.Coprime b (2 * p - 1) := hcop.coprime_mul_left_right
  have hb0_nat : (b : ZMod (2 * p - 1)) ≠ 0 := zmod_natCast_ne_zero_of_coprime hq hcop_bq
  have hb0 : ((b : ℤ) : ZMod (2 * p - 1)) ≠ 0 := by simpa using hb0_nat
  rw [legendreSym.eq_one_iff (p := 2 * p - 1) hb0,
    ZMod.euler_criterion (2 * p - 1) hb0]
  have hdiv : (2 * p - 1) / 2 = p - 1 := by have := hp.two_le; omega
  rw [hdiv, Int.cast_natCast, ← ZMod.natCast_eq_natCast_iff, Nat.cast_pow, Nat.cast_one]

/-- **Theorem 2(3), 2-adic order form**: For `IsK2Number n p` with odd prime `p` and
`Nat.Coprime b n`, `IsStrongProbablePrime n b` holds iff the 2-adic valuation of
`orderOf (b : ZMod p)` equals that of `orderOf (b : ZMod (2p - 1))`. -/
theorem k2_sprp_iff_two_adic_order {n p b : ℕ} (hk2 : IsK2Number n p) (hp_odd : Odd p)
    (hcop : Nat.Coprime b n) :
    IsStrongProbablePrime n b ↔
      padicValNat 2 (orderOf (b : ZMod p)) =
        padicValNat 2 (orderOf (b : ZMod (2 * p - 1))) := by
  have hcop_pq : Nat.Coprime p (2 * p - 1) := k2_coprime_factors hk2
  have hq_odd : Odd (2 * p - 1) := ⟨p - 1, by have := hk2.1.two_le; omega⟩
  constructor
  · exact semiprime_padicValNat_orderOf_eq_of_sprp hk2.1 hk2.2.1 hp_odd hq_odd hk2.2.2
  · intro heq_val
    have hp_pos : 0 < p - 1 := by have := hk2.1.two_le; omega
    obtain ⟨m, hm_odd, hm_eq⟩ := exists_eq_two_pow_padicValNat_mul_odd hp_pos
    set e := padicValNat 2 (p - 1)
    set d := (2 * p + 1) * m
    obtain ⟨hn_decomp, hd_odd, hq_decomp⟩ := k2_two_adic_decomp hk2 hm_odd hm_eq
    have hn_odd : Odd n := by rw [hk2.2.2]; exact hp_odd.mul hq_odd
    have hn_ge3 : 3 ≤ n := by
      rcases hp_odd with ⟨k, hk⟩
      have hp3 : 3 ≤ p := by have := hk2.1.two_le; omega
      have hq5 : 5 ≤ 2 * p - 1 := by omega
      nlinarith [hk2.2.2]
    rw [isStrongProbablePrime_iff_of_decomp hn_odd hn_ge3 hd_odd hn_decomp]
    have hcop_bp : Nat.Coprime b p := by rw [hk2.2.2] at hcop; exact hcop.coprime_mul_right_right
    have hcop_bq : Nat.Coprime b (2 * p - 1) := by
      rw [hk2.2.2] at hcop; exact hcop.coprime_mul_left_right
    obtain ⟨up, hup_odd, hup_eq⟩ :=
      exists_eq_two_pow_padicValNat_mul_odd (orderOf_zmod_pos hk2.1 hcop_bp)
    obtain ⟨uq, huq_odd, huq_eq⟩ :=
      exists_eq_two_pow_padicValNat_mul_odd (orderOf_zmod_pos hk2.2.1 hcop_bq)
    rw [← heq_val] at huq_eq
    set t := padicValNat 2 (orderOf (b : ZMod p))
    have ht_le : t ≤ e := padicValNat_orderOf_le hk2.1 hcop_bp
    have hup_dvd_d : up ∣ d := by
      have hdvd_pm1 := hm_eq ▸ orderOf_zmod_dvd_pred hk2.1 hcop_bp
      have hup_m : up ∣ m :=
        odd_dvd_of_dvd_two_pow_mul hup_odd
          (dvd_trans ⟨2 ^ t, hup_eq.trans (mul_comm _ _)⟩ hdvd_pm1)
      exact dvd_mul_of_dvd_right hup_m (2 * p + 1)
    have huq_dvd_d : uq ∣ d := by
      have hdvd_qm1 := hq_decomp ▸ orderOf_zmod_dvd_pred hk2.2.1 hcop_bq
      have huq_m : uq ∣ m :=
        odd_dvd_of_dvd_two_pow_mul huq_odd
          (dvd_trans ⟨2 ^ t, huq_eq.trans (mul_comm _ _)⟩ hdvd_qm1)
      exact dvd_mul_of_dvd_right huq_m (2 * p + 1)
    by_cases ht0 : t = 0
    · left
      have hp1 : b ^ d ≡ 1 [MOD p] := by
        rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_pow, Nat.cast_one,
          ← orderOf_dvd_iff_pow_eq_one, hup_eq, ht0, pow_zero, one_mul]
        exact hup_dvd_d
      have hq1 : b ^ d ≡ 1 [MOD (2 * p - 1)] := by
        rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_pow, Nat.cast_one,
          ← orderOf_dvd_iff_pow_eq_one, huq_eq, ht0, pow_zero, one_mul]
        exact huq_dvd_d
      have hmn := (Nat.modEq_and_modEq_iff_modEq_mul hcop_pq).mp ⟨hp1, hq1⟩
      rwa [← hk2.2.2] at hmn
    · right
      set k := t - 1
      have htk : t = k + 1 := by omega
      refine ⟨k, by omega, ?_⟩
      have hpow_neg : ∀ {r u : ℕ}, Nat.Prime r → Odd u → u ∣ d →
          orderOf (b : ZMod r) = 2 ^ (k + 1) * u →
          (b : ZMod r) ^ (2 ^ k * d) = -1 := by
        intro r u hr hu_odd hu_d hord_eq
        have : Fact r.Prime := ⟨hr⟩
        have hsq : ((b : ZMod r) ^ (2 ^ k * d)) ^ 2 = 1 := by
          rw [← pow_mul]
          have hexp : 2 ^ k * d * 2 = 2 ^ (k + 1) * d := by rw [pow_succ]; ring
          rw [hexp, ← orderOf_dvd_iff_pow_eq_one, hord_eq]
          exact mul_dvd_mul_left (2 ^ (k + 1)) hu_d
        rcases sq_eq_one_iff.mp hsq with h1 | hneg1
        · exfalso
          have hdvd_k : 2 ^ (k + 1) * u ∣ 2 ^ k * d := by
            rw [← hord_eq, orderOf_dvd_iff_pow_eq_one]
            exact h1
          have hle : k + 1 ≤ k :=
            two_pow_le_of_dvd_two_pow_mul_odd hd_odd (dvd_trans ⟨u, rfl⟩ hdvd_k)
          omega
        · exact hneg1
      have hp_neg : b ^ (2 ^ k * d) ≡ n - 1 [MOD p] := by
        rw [zmod_modEq_pred_iff_eq_neg_one (by omega : 1 ≤ n) ⟨2 * p - 1, hk2.2.2⟩, Nat.cast_pow]
        exact hpow_neg hk2.1 hup_odd hup_dvd_d (htk ▸ hup_eq)
      have hq_neg : b ^ (2 ^ k * d) ≡ n - 1 [MOD (2 * p - 1)] := by
        rw [zmod_modEq_pred_iff_eq_neg_one (by omega : 1 ≤ n) ⟨p, by rw [hk2.2.2, mul_comm]⟩,
          Nat.cast_pow]
        exact hpow_neg hk2.2.1 huq_odd huq_dvd_d (htk ▸ huq_eq)
      have hmn := (Nat.modEq_and_modEq_iff_modEq_mul hcop_pq).mp ⟨hp_neg, hq_neg⟩
      rwa [← hk2.2.2] at hmn

/-- **Theorem 2(3), 2-power residue level form**: For `IsK2Number n p` with odd prime `p`
and `Nat.Coprime b n`, `n` is a strong probable prime to base `b` iff
`j_{2p - 1}(b) = j_p(b) + 1`. -/
theorem k2_sprp_iff_level {n p b : ℕ} (hk2 : IsK2Number n p) (hp_odd : Odd p)
    (hcop : Nat.Coprime b n) :
    IsStrongProbablePrime n b ↔ twoPowLevel (2 * p - 1) b = twoPowLevel p b + 1 := by
  rw [k2_sprp_iff_two_adic_order hk2 hp_odd hcop]
  have hcop_bp : Nat.Coprime b p := by rw [hk2.2.2] at hcop; exact hcop.coprime_mul_right_right
  have hcop_bq : Nat.Coprime b (2 * p - 1) := by
    rw [hk2.2.2] at hcop; exact hcop.coprime_mul_left_right
  have hp_rel := twoPowLevel_add_padicValNat_orderOf hk2.1 hcop_bp
  have hq_rel := twoPowLevel_add_padicValNat_orderOf hk2.2.1 hcop_bq
  have hqm1 := (k2_padicValNat_pred hk2).2
  omega

/-! ## 5. Corollary 3 (`cor:k2-liars`): Base-2 Obstruction and Exact Strong-Liar Density -/

/-- **Corollary 3(2), base-2 obstruction**: If `IsK2Number n p` and `p ≡ 3 (mod 4)`,
then `n` is never a strong probable prime to base `2`. -/
theorem k2_not_sprp_two_of_mod_four_eq_three {n p : ℕ} (hk2 : IsK2Number n p)
    (hp3 : p % 4 = 3) : ¬ IsStrongProbablePrime n 2 := by
  intro hsprp
  have hfermat : 2 ^ (n - 1) ≡ 1 [MOD n] := isStrongProbablePrime_implies_fermat hsprp
  have hp_odd : Odd p := Nat.odd_iff.mpr (by omega)
  have hq_odd : Odd (2 * p - 1) := ⟨p - 1, by omega⟩
  have hn_odd : Odd n := by rw [hk2.2.2]; exact hp_odd.mul hq_odd
  have hcop2 : Nat.Coprime 2 n := Nat.coprime_two_left.mpr hn_odd
  have : Fact (Nat.Prime (2 * p - 1)) := ⟨hk2.2.1⟩
  have hleg : legendreSym (2 * p - 1) 2 = 1 :=
    (k2_fermat_iff_legendre hk2 hcop2).mp hfermat
  have h2_ne0 : ((2 : ℤ) : ZMod (2 * p - 1)) ≠ 0 := by
    simpa using zmod_natCast_ne_zero_of_coprime hk2.2.1
      (Nat.coprime_two_left.mpr hq_odd)
  have hsq : IsSquare (2 : ZMod (2 * p - 1)) := by
    simpa using (legendreSym.eq_one_iff (p := 2 * p - 1) h2_ne0).mp hleg
  have hq_ne2 : 2 * p - 1 ≠ 2 := by omega
  have hq8 : (2 * p - 1) % 8 = 1 ∨ (2 * p - 1) % 8 = 7 :=
    (ZMod.exists_sq_eq_two_iff hq_ne2).mp hsq
  omega

/-- **Corollary 3(2), residue consequences**: Every `K2` strong probable prime to base `2`
satisfies `p ≡ 1 (mod 4)`, `2p - 1 ≡ 1 (mod 8)`, and `n ≡ 1 (mod 4)`. -/
theorem k2_mod_of_sprp_two {n p : ℕ} (hk2 : IsK2Number n p)
    (hsprp : IsStrongProbablePrime n 2) :
    p % 4 = 1 ∧ (2 * p - 1) % 8 = 1 ∧ n % 4 = 1 := by
  have hn_odd : Odd n := hsprp.1
  have hp_odd : Odd p := by
    by_contra hp_even
    rw [Nat.not_odd_iff_even] at hp_even
    rcases hp_even with ⟨k, hk⟩
    have hn_even : Even n := ⟨k * (2 * p - 1), by rw [hk2.2.2, hk]; ring⟩
    exact (Nat.not_odd_iff_even.mpr hn_even) hn_odd
  have hp_not3 : p % 4 ≠ 3 :=
    fun hp3 => k2_not_sprp_two_of_mod_four_eq_three hk2 hp3 hsprp
  have hp1 : p % 4 = 1 := by rcases hp_odd with ⟨k, hk⟩; omega
  have hq1 : (2 * p - 1) % 8 = 1 := by omega
  have hn1 : n % 4 = 1 := by
    rw [hk2.2.2, Nat.mul_mod, hp1]
    have hq4 : (2 * p - 1) % 4 = 1 := by omega
    rw [hq4]
  exact ⟨hp1, hq1, hn1⟩

/-- The finite set of strong-liar bases `b ∈ {0, …, n - 1}` coprime to `n`. -/
noncomputable def strongLiarFinset (n : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range n).filter (fun b => Nat.Coprime b n ∧ IsStrongProbablePrime n b)

/-- Number of units `b ∈ (ℤ/nℤ)ˣ` (represented in `{0, …, n - 1}`) for which `n` passes
the strong probable prime test. -/
noncomputable def strongLiarCount (n : ℕ) : ℕ :=
  (strongLiarFinset n).card

/-- In a finite cyclic group `G`, for every divisor `d ∣ |G|` with `d ≠ 0`,
exactly `d` elements satisfy `u ^ d = 1`. -/
theorem cyclic_card_pow_eq_one {G : Type*} [Group G] [IsCyclic G] [Fintype G] [DecidableEq G]
    {d : ℕ} (hd : d ∣ Fintype.card G) (hd0 : d ≠ 0) :
    (Finset.univ.filter (fun u : G => u ^ d = 1)).card = d := by
  calc
    (Finset.univ.filter (fun u : G => u ^ d = 1)).card
        = ∑ m ∈ d.divisors, (Finset.univ.filter (fun u : G => orderOf u = m)).card :=
          (sum_card_orderOf_eq_card_pow_eq_one hd0).symm
    _ = ∑ m ∈ d.divisors, m.totient :=
          Finset.sum_congr rfl fun m hm =>
            IsCyclic.card_orderOf_eq_totient ((Nat.dvd_of_mem_divisors hm).trans hd)
    _ = d := Nat.sum_totient d

private theorem cyclic_card_two_adic_order_le {G : Type*} [Group G] [IsCyclic G]
    [Fintype G] [DecidableEq G] {E m k : ℕ} (hm : Odd m)
    (hcard : Fintype.card G = 2 ^ E * m) (hk : k ≤ E) :
    (Finset.univ.filter (fun u : G => padicValNat 2 (orderOf u) ≤ k)).card = 2 ^ k * m := by
  have hm_pos : 0 < m := by rcases hm with ⟨j, rfl⟩; omega
  have hfilt : Finset.univ.filter (fun u : G => padicValNat 2 (orderOf u) ≤ k) =
      Finset.univ.filter (fun u : G => u ^ (2 ^ k * m) = 1) := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, ← orderOf_dvd_iff_pow_eq_one]
    have hord_dvd : orderOf u ∣ 2 ^ E * m := hcard ▸ orderOf_dvd_card
    have hord_pos : 0 < orderOf u := orderOf_pos u
    obtain ⟨w, hw_odd, hw_eq⟩ := exists_eq_two_pow_padicValNat_mul_odd hord_pos
    have hw_m : w ∣ m :=
      odd_dvd_of_dvd_two_pow_mul hw_odd
        (dvd_trans ⟨2 ^ padicValNat 2 (orderOf u), hw_eq.trans (mul_comm _ _)⟩ hord_dvd)
    constructor
    · intro hle
      rw [hw_eq]
      exact mul_dvd_mul (pow_dvd_pow 2 hle) hw_m
    · intro hdvd
      rw [hw_eq] at hdvd
      exact two_pow_le_of_dvd_two_pow_mul_odd hm (dvd_trans ⟨w, rfl⟩ hdvd)
  rw [hfilt]
  have hdvd : 2 ^ k * m ∣ Fintype.card G := by
    rw [hcard]
    exact mul_dvd_mul_right (pow_dvd_pow 2 hk) m
  exact cyclic_card_pow_eq_one hdvd (by positivity)

/-- In `(ZMod r)ˣ` for prime `r` with `r - 1 = 2 ^ E * m` (`m` odd), exactly `m` units
have odd multiplicative order (`v_2(ord_r(u)) = 0`). -/
theorem zmod_units_card_two_adic_order_zero {r E m : ℕ} [Fact r.Prime] (hm : Odd m)
    (hrm1 : r - 1 = 2 ^ E * m) :
    (Finset.univ.filter (fun u : (ZMod r)ˣ => padicValNat 2 (orderOf u) = 0)).card = m := by
  have hcard : Fintype.card (ZMod r)ˣ = 2 ^ E * m := by
    rw [ZMod.card_units_eq_totient, Nat.totient_prime Fact.out, hrm1]
  have hle0 : Finset.univ.filter (fun u : (ZMod r)ˣ => padicValNat 2 (orderOf u) = 0) =
      Finset.univ.filter (fun u : (ZMod r)ˣ => padicValNat 2 (orderOf u) ≤ 0) := by
    ext u; simp
  rw [hle0, cyclic_card_two_adic_order_le hm hcard (Nat.zero_le E), pow_zero, one_mul]

/-- In `(ZMod r)ˣ` for prime `r` with `r - 1 = 2 ^ E * m` (`m` odd) and `k < E`,
exactly `2 ^ k * m` units satisfy `v_2(ord_r(u)) = k + 1`. -/
theorem zmod_units_card_two_adic_order_succ {r E m k : ℕ} [Fact r.Prime] (hm : Odd m)
    (hrm1 : r - 1 = 2 ^ E * m) (hk : k < E) :
    (Finset.univ.filter (fun u : (ZMod r)ˣ => padicValNat 2 (orderOf u) = k + 1)).card =
      2 ^ k * m := by
  have hcard : Fintype.card (ZMod r)ˣ = 2 ^ E * m := by
    rw [ZMod.card_units_eq_totient, Nat.totient_prime Fact.out, hrm1]
  set S_succ := Finset.univ.filter (fun u : (ZMod r)ˣ => padicValNat 2 (orderOf u) ≤ k + 1)
  set S_k := Finset.univ.filter (fun u : (ZMod r)ˣ => padicValNat 2 (orderOf u) ≤ k)
  have hsub : S_k ⊆ S_succ := by
    intro u hu
    simp only [S_k, S_succ, Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
    omega
  have hsdiff : Finset.univ.filter (fun u : (ZMod r)ˣ => padicValNat 2 (orderOf u) = k + 1) =
      S_succ \ S_k := by
    ext u
    simp only [S_succ, S_k, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  rw [hsdiff, Finset.card_sdiff, Finset.inter_eq_left.mpr hsub,
    cyclic_card_two_adic_order_le hm hcard (Nat.succ_le_of_lt hk),
    cyclic_card_two_adic_order_le hm hcard (le_of_lt hk),
    pow_succ]
  have h2km : 2 ^ k * 2 * m = 2 ^ k * m + 2 ^ k * m := by ring
  rw [h2km, Nat.add_sub_cancel]

private theorem geom_sum_four (e : ℕ) :
    3 * (∑ k ∈ Finset.range e, 4 ^ k) + 1 = 4 ^ e := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [Finset.sum_range_succ, pow_succ]
    linarith

/-- **Corollary 3(1), exact odd-part count**: For `IsK2Number n p` with odd prime `p`
and `p - 1 = 2 ^ e * m` (`m` odd), `3 * strongLiarCount n = (4 ^ e + 2) * m ^ 2`. -/
theorem k2_strongLiarCount_mul_three {n p e m : ℕ} (hk2 : IsK2Number n p) (hp_odd : Odd p)
    (hm : Odd m) (hp_decomp : p - 1 = 2 ^ e * m) :
    3 * strongLiarCount n = (4 ^ e + 2) * m ^ 2 := by
  classical
  set q := 2 * p - 1
  have hcop_pq : Nat.Coprime p q := k2_coprime_factors hk2
  obtain ⟨_, _, hq_decomp⟩ := k2_two_adic_decomp hk2 hm hp_decomp
  have : Fact p.Prime := ⟨hk2.1⟩
  have : Fact q.Prime := ⟨hk2.2.1⟩
  have : NeZero p := ⟨hk2.1.ne_zero⟩
  have : NeZero q := ⟨hk2.2.1.ne_zero⟩
  set P := (Finset.univ : Finset ((ZMod p)ˣ × (ZMod q)ˣ)).filter
    (fun uv => padicValNat 2 (orderOf uv.1) = padicValNat 2 (orderOf uv.2))
  have hbij : strongLiarCount n = P.card := by
    unfold strongLiarCount strongLiarFinset
    refine Finset.card_bij
      (fun b hb =>
        let hcop : Nat.Coprime b n := (Finset.mem_filter.mp hb).2.1
        (ZMod.unitOfCoprime b (by rw [hk2.2.2] at hcop; exact hcop.coprime_mul_right_right),
         ZMod.unitOfCoprime b (by rw [hk2.2.2] at hcop; exact hcop.coprime_mul_left_right)))
      ?_ ?_ ?_
    · intro b hb
      rcases Finset.mem_filter.mp hb with ⟨_, hcop, hsprp⟩
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      have hord_p : orderOf (ZMod.unitOfCoprime b
          (by rw [hk2.2.2] at hcop; exact hcop.coprime_mul_right_right)) =
          orderOf (b : ZMod p) := by
        rw [← orderOf_units, ZMod.coe_unitOfCoprime]
      have hord_q : orderOf (ZMod.unitOfCoprime b
          (by rw [hk2.2.2] at hcop; exact hcop.coprime_mul_left_right)) =
          orderOf (b : ZMod q) := by
        rw [← orderOf_units, ZMod.coe_unitOfCoprime]
      rw [hord_p, hord_q]
      exact (k2_sprp_iff_two_adic_order hk2 hp_odd hcop).mp hsprp
    · intro b₁ hb₁ b₂ hb₂ heq
      have h1lt : b₁ < n := Finset.mem_range.mp (Finset.mem_filter.mp hb₁).1
      have h2lt : b₂ < n := Finset.mem_range.mp (Finset.mem_filter.mp hb₂).1
      have hp_eq : (b₁ : ZMod p) = (b₂ : ZMod p) := by
        have h := congrArg (fun x : (ZMod p)ˣ × (ZMod q)ˣ => (x.1 : ZMod p)) heq
        simpa [ZMod.coe_unitOfCoprime] using h
      have hq_eq : (b₁ : ZMod q) = (b₂ : ZMod q) := by
        have h := congrArg (fun x : (ZMod p)ˣ × (ZMod q)ˣ => (x.2 : ZMod q)) heq
        simpa [ZMod.coe_unitOfCoprime] using h
      have hmod_p : b₁ ≡ b₂ [MOD p] := (ZMod.natCast_eq_natCast_iff b₁ b₂ p).mp hp_eq
      have hmod_q : b₁ ≡ b₂ [MOD q] := (ZMod.natCast_eq_natCast_iff b₁ b₂ q).mp hq_eq
      have hmod_n : b₁ ≡ b₂ [MOD n] := by
        rw [hk2.2.2]
        exact (Nat.modEq_and_modEq_iff_modEq_mul hcop_pq).mp ⟨hmod_p, hmod_q⟩
      change b₁ % n = b₂ % n at hmod_n
      rwa [Nat.mod_eq_of_lt h1lt, Nat.mod_eq_of_lt h2lt] at hmod_n
    · intro ⟨u, v⟩ huv
      have heq_ord : padicValNat 2 (orderOf u) = padicValNat 2 (orderOf v) :=
        (Finset.mem_filter.mp huv).2
      let crt := ZMod.chineseRemainder hcop_pq
      let z_pq : ZMod (p * q) := crt.symm ((u : ZMod p), (v : ZMod q))
      let b : ℕ := z_pq.val
      have : NeZero (p * q) := ⟨mul_ne_zero hk2.1.ne_zero hk2.2.1.ne_zero⟩
      have hb_lt : b < n := by rw [hk2.2.2]; exact ZMod.val_lt z_pq
      have hcrt_z : crt z_pq = ((u : ZMod p), (v : ZMod q)) := crt.apply_symm_apply _
      have hbp_cast : (b : ZMod p) = (u : ZMod p) := by
        have h1 : (z_pq : ZMod (p * q)) = (b : ZMod (p * q)) := (ZMod.natCast_zmod_val z_pq).symm
        have h2 : (crt (b : ZMod (p * q))).1 = (u : ZMod p) := by
          rw [← h1, hcrt_z]
        simpa using h2
      have hbq_cast : (b : ZMod q) = (v : ZMod q) := by
        have h1 : (z_pq : ZMod (p * q)) = (b : ZMod (p * q)) := (ZMod.natCast_zmod_val z_pq).symm
        have h2 : (crt (b : ZMod (p * q))).2 = (v : ZMod q) := by
          rw [← h1, hcrt_z]
        simpa using h2
      have hcop_bp : Nat.Coprime b p := by
        rw [Nat.coprime_comm, hk2.1.coprime_iff_not_dvd]
        intro hdvd
        exact u.ne_zero (hbp_cast.symm.trans ((ZMod.natCast_eq_zero_iff b p).mpr hdvd))
      have hcop_bq : Nat.Coprime b q := by
        rw [Nat.coprime_comm, hk2.2.1.coprime_iff_not_dvd]
        intro hdvd
        exact v.ne_zero (hbq_cast.symm.trans ((ZMod.natCast_eq_zero_iff b q).mpr hdvd))
      have hcop_bn : Nat.Coprime b n := by
        rw [hk2.2.2]
        exact hcop_bp.mul_right hcop_bq
      have hord_p : orderOf (b : ZMod p) = orderOf u := by
        rw [hbp_cast, orderOf_units]
      have hord_q : orderOf (b : ZMod q) = orderOf v := by
        rw [hbq_cast, orderOf_units]
      have hsprp : IsStrongProbablePrime n b :=
        (k2_sprp_iff_two_adic_order hk2 hp_odd hcop_bn).mpr (by rw [hord_p, hord_q, heq_ord])
      refine ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hb_lt, hcop_bn, hsprp⟩, ?_⟩
      ext <;> simp [ZMod.coe_unitOfCoprime, hbp_cast, hbq_cast]
  rw [hbij]
  have hpart : P = (Finset.range (e + 1)).biUnion (fun t =>
      (Finset.univ.filter (fun u : (ZMod p)ˣ => padicValNat 2 (orderOf u) = t)) ×ˢ
      (Finset.univ.filter (fun v : (ZMod q)ˣ => padicValNat 2 (orderOf v) = t))) := by
    ext ⟨u, v⟩
    simp only [P, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
      Finset.mem_range, Finset.mem_product]
    constructor
    · intro heq
      have hcard_p : Fintype.card (ZMod p)ˣ = 2 ^ e * m := by
        rw [ZMod.card_units_eq_totient, Nat.totient_prime hk2.1, hp_decomp]
      have hord_dvd : orderOf u ∣ 2 ^ e * m := hcard_p ▸ orderOf_dvd_card
      obtain ⟨w, _, hw_eq⟩ := exists_eq_two_pow_padicValNat_mul_odd (orderOf_pos u)
      have hle : padicValNat 2 (orderOf u) ≤ e :=
        two_pow_le_of_dvd_two_pow_mul_odd hm (dvd_trans ⟨w, hw_eq⟩ hord_dvd)
      exact ⟨padicValNat 2 (orderOf u), Nat.lt_succ_of_le hle, rfl, heq.symm⟩
    · rintro ⟨t, _, rfl, hv⟩
      exact hv.symm
  have hdisj : Set.PairwiseDisjoint (Finset.range (e + 1) : Set ℕ) (fun t =>
      (Finset.univ.filter (fun u : (ZMod p)ˣ => padicValNat 2 (orderOf u) = t)) ×ˢ
      (Finset.univ.filter (fun v : (ZMod q)ˣ => padicValNat 2 (orderOf v) = t))) := by
    intro t₁ _ t₂ _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro ⟨u, v⟩ h1 h2
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    exact hne (h1.1.symm.trans h2.1)
  have hcard_P : P.card =
      m ^ 2 + ∑ k ∈ Finset.range e, (2 ^ k * m) * (2 ^ k * m) := by
    rw [hpart, Finset.card_biUnion hdisj, Finset.sum_range_succ', add_comm]
    congr 1
    · rw [Finset.card_product, zmod_units_card_two_adic_order_zero hm hp_decomp,
        zmod_units_card_two_adic_order_zero hm hq_decomp, sq]
    · refine Finset.sum_congr rfl fun k hk => ?_
      have hk_lt : k < e := Finset.mem_range.mp hk
      rw [Finset.card_product,
        zmod_units_card_two_adic_order_succ hm hp_decomp hk_lt,
        zmod_units_card_two_adic_order_succ hm hq_decomp (by omega : k < e + 1)]
  have hfactor : ∑ k ∈ Finset.range e, (2 ^ k * m) * (2 ^ k * m) =
      (∑ k ∈ Finset.range e, 4 ^ k) * m ^ 2 := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    have h4 : (2 ^ k) * (2 ^ k) = 4 ^ k := by
      rw [← mul_pow]
      norm_num
    calc
      (2 ^ k * m) * (2 ^ k * m) = ((2 ^ k) * (2 ^ k)) * m ^ 2 := by ring
      _ = 4 ^ k * m ^ 2 := by rw [h4]
  rw [hcard_P, hfactor]
  have hg := geom_sum_four e
  nlinarith

/-- **Corollary 3(1), totient equation**: For `IsK2Number n p` with odd prime `p`
and `e = padicValNat 2 (p - 1)`,
`6 * 4 ^ e * strongLiarCount n = (4 ^ e + 2) * Nat.totient n`. -/
theorem k2_strongLiarCount_eq {n p : ℕ} (hk2 : IsK2Number n p) (hp_odd : Odd p) :
    6 * 4 ^ padicValNat 2 (p - 1) * strongLiarCount n =
      (4 ^ padicValNat 2 (p - 1) + 2) * Nat.totient n := by
  have hp_pos : 0 < p - 1 := by have := hk2.1.two_le; omega
  obtain ⟨m, hm_odd, hm_eq⟩ := exists_eq_two_pow_padicValNat_mul_odd hp_pos
  set e := padicValNat 2 (p - 1)
  have h3 : 3 * strongLiarCount n = (4 ^ e + 2) * m ^ 2 :=
    k2_strongLiarCount_mul_three hk2 hp_odd hm_odd hm_eq
  obtain ⟨_, _, hq_eq⟩ := k2_two_adic_decomp hk2 hm_odd hm_eq
  have htot : Nat.totient n = 2 * 4 ^ e * m ^ 2 := by
    have hcop_pq : Nat.Coprime p (2 * p - 1) := k2_coprime_factors hk2
    rw [hk2.2.2, Nat.totient_mul hcop_pq, Nat.totient_prime hk2.1,
      Nat.totient_prime hk2.2.1, hm_eq, hq_eq, pow_succ']
    have h4 : (2 ^ e) * (2 ^ e) = 4 ^ e := by rw [← mul_pow]; norm_num
    calc
      (2 ^ e * m) * (2 * 2 ^ e * m) = 2 * ((2 ^ e) * (2 ^ e)) * m ^ 2 := by ring
      _ = 2 * 4 ^ e * m ^ 2 := by rw [h4]
  rw [htot]
  calc
    6 * 4 ^ e * strongLiarCount n
        = 2 * 4 ^ e * (3 * strongLiarCount n) := by ring
    _ = 2 * 4 ^ e * ((4 ^ e + 2) * m ^ 2) := by rw [h3]
    _ = (4 ^ e + 2) * (2 * 4 ^ e * m ^ 2) := by ring

/-- **Corollary 3(1), rational fraction**: For `IsK2Number n p` with odd prime `p`
and `e = padicValNat 2 (p - 1)`, the fraction of units `b ∈ (ℤ/nℤ)ˣ` that are strong liars
equals `(1 + 2 * 4 ^ (-e)) / 6`. -/
theorem k2_strongLiar_share_rat {n p : ℕ} (hk2 : IsK2Number n p) (hp_odd : Odd p) :
    (strongLiarCount n : ℚ) / (Nat.totient n : ℚ) =
      (1 + 2 * (4 : ℚ) ^ (-(padicValNat 2 (p - 1) : ℤ))) / 6 := by
  set e := padicValNat 2 (p - 1)
  have hn_pos : 0 < n := by rw [hk2.2.2]; exact Nat.mul_pos hk2.1.pos hk2.2.1.pos
  have htot_ne : (Nat.totient n : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr hn_pos).ne'
  have h4_ne : ((4 : ℚ) ^ e) ≠ 0 := by positivity
  have heq : (6 : ℚ) * (4 : ℚ) ^ e * (strongLiarCount n : ℚ) =
      ((4 : ℚ) ^ e + 2) * (Nat.totient n : ℚ) := by
    exact_mod_cast k2_strongLiarCount_eq hk2 hp_odd
  rw [zpow_neg, zpow_natCast]
  field_simp [htot_ne, h4_ne]
  linarith

/-- **Corollary 3(1), `e = 1` specialization**: When `p ≡ 3 (mod 4)`, the strong-liar fraction
of a `K2` number is `1 / 4`. -/
theorem k2_strongLiar_share_e1 {n p : ℕ} (hk2 : IsK2Number n p) (hp3 : p % 4 = 3) :
    (strongLiarCount n : ℚ) / (Nat.totient n : ℚ) = 1 / 4 := by
  have hp_odd : Odd p := Nat.odd_iff.mpr (by omega)
  have he1 : padicValNat 2 (p - 1) = 1 := by
    have hm_odd : Odd ((p - 1) / 2) := Nat.odd_iff.mpr (by omega)
    exact padicValNat_two_pow_mul_odd hm_odd (by omega : p - 1 = 2 ^ 1 * ((p - 1) / 2))
  rw [k2_strongLiar_share_rat hk2 hp_odd, he1]
  norm_num

/-- **Corollary 3(1), `e = 2` specialization**: When `padicValNat 2 (p - 1) = 2`,
the strong-liar fraction of a `K2` number is `3 / 16`. -/
theorem k2_strongLiar_share_e2 {n p : ℕ} (hk2 : IsK2Number n p)
    (he2 : padicValNat 2 (p - 1) = 2) :
    (strongLiarCount n : ℚ) / (Nat.totient n : ℚ) = 3 / 16 := by
  have hp_odd : Odd p := by
    have hp_pos : 0 < p - 1 := by have := hk2.1.two_le; omega
    obtain ⟨m, _, hm_eq⟩ := exists_eq_two_pow_padicValNat_mul_odd hp_pos
    rw [he2] at hm_eq
    exact ⟨2 * m, by omega⟩
  rw [k2_strongLiar_share_rat hk2 hp_odd, he2]
  norm_num

/-- **Corollary 3(2), liar-density upper bound**: Every `K2` strong probable prime to base `2`
has strong-liar fraction at most `3 / 16`. -/
theorem k2_strongLiar_share_le_of_sprp_two {n p : ℕ} (hk2 : IsK2Number n p)
    (hsprp2 : IsStrongProbablePrime n 2) :
    (strongLiarCount n : ℚ) / (Nat.totient n : ℚ) ≤ 3 / 16 := by
  obtain ⟨hp1, _, _⟩ := k2_mod_of_sprp_two hk2 hsprp2
  have hp_odd : Odd p := Nat.odd_iff.mpr (by omega)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h4_dvd : 2 ^ 2 ∣ p - 1 := ⟨(p - 1) / 4, by omega⟩
  have he_ge2 : 2 ≤ padicValNat 2 (p - 1) :=
    (padicValNat_dvd_iff_le (by have := hk2.1.two_le; omega)).mp h4_dvd
  rw [k2_strongLiar_share_rat hk2 hp_odd, zpow_neg, zpow_natCast]
  have h16_le : (16 : ℚ) ≤ (4 : ℚ) ^ padicValNat 2 (p - 1) := by
    calc
      (16 : ℚ) = (4 : ℚ) ^ 2 := by norm_num
      _ ≤ (4 : ℚ) ^ padicValNat 2 (p - 1) :=
        pow_le_pow_right₀ (by norm_num : (1 : ℚ) ≤ 4) he_ge2
  have hinv_le : ((4 : ℚ) ^ padicValNat 2 (p - 1))⁻¹ ≤ (16 : ℚ)⁻¹ :=
    inv_anti₀ (by norm_num : (0 : ℚ) < 16) h16_le
  linarith

/-! ## 6. Lemma 4 (`lem:k-gen`): Quadratic-Residue Criterion for General `K_{a/b}` Forms -/

/-- Parameterization of `K_{a/b}` primes: if `b(q - 1) = a(p - 1)` with `0 < b`,
`gcd(a, b) = 1`, and `2 ≤ p`, then there exists `m > 0` with `p - 1 = bm` and `q - 1 = am`. -/
theorem exists_k_gen_param {p q a b : ℕ} (hp : 2 ≤ p) (hb : 0 < b)
    (hcop : Nat.Coprime a b) (hrel : b * (q - 1) = a * (p - 1)) :
    ∃ m : ℕ, 0 < m ∧ p - 1 = b * m ∧ q - 1 = a * m := by
  have hb_dvd_prod : b ∣ a * (p - 1) := ⟨q - 1, hrel.symm⟩
  rcases hcop.symm.dvd_of_dvd_mul_left hb_dvd_prod with ⟨m, hpm1⟩
  have hm_pos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with rfl | hpos
    · rw [mul_zero] at hpm1
      omega
    · exact hpos
  have hqm1 : q - 1 = a * m := by
    apply Nat.eq_of_mul_eq_mul_left hb
    calc
      b * (q - 1) = a * (p - 1) := hrel
      _ = a * (b * m) := by rw [hpm1]
      _ = b * (a * m) := by ring
  exact ⟨m, hm_pos, hpm1, hqm1⟩

/-- Euler's criterion in 2-adic valuation form: for an odd prime `r` and `Nat.Coprime c r`,
`legendreSym r c = -1` iff `v_2(ord_r(c)) = v_2(r - 1)`. -/
theorem legendreSym_eq_neg_one_iff_padicValNat_orderOf {r c : ℕ} [Fact r.Prime]
    (hr_odd : Odd r) (hcop : Nat.Coprime c r) :
    legendreSym r (c : ℤ) = -1 ↔
      padicValNat 2 (orderOf (c : ZMod r)) = padicValNat 2 (r - 1) := by
  have hr : Nat.Prime r := Fact.out
  have hc0_nat : (c : ZMod r) ≠ 0 := zmod_natCast_ne_zero_of_coprime hr hcop
  have hc0 : ((c : ℤ) : ZMod r) ≠ 0 := by simpa using hc0_nat
  rw [legendreSym.eq_neg_one_iff (p := r), ZMod.euler_criterion r hc0,
    Int.cast_natCast, ← orderOf_dvd_iff_pow_eq_one]
  have hpos_rm1 : 0 < r - 1 := by have := hr.two_le; omega
  obtain ⟨m, hm_odd, hm_eq⟩ := exists_eq_two_pow_padicValNat_mul_odd hpos_rm1
  set E := padicValNat 2 (r - 1)
  have hE_pos : 1 ≤ E := by
    by_contra hE0
    have h0 : E = 0 := by omega
    rw [h0, pow_zero, one_mul] at hm_eq
    rcases hr_odd with ⟨k, hk⟩
    rcases hm_odd with ⟨j, hj⟩
    omega
  have hr_div2 : r / 2 = 2 ^ (E - 1) * m := by
    have hr_sub : r / 2 = (r - 1) / 2 := by rcases hr_odd with ⟨k, hk⟩; omega
    have hexp : E = 1 + (E - 1) := by omega
    have hrm1_2 : r - 1 = 2 * (2 ^ (E - 1) * m) := by
      calc
        r - 1 = 2 ^ E * m := hm_eq
        _ = 2 ^ (1 + (E - 1)) * m := by rw [← hexp]
        _ = 2 * (2 ^ (E - 1) * m) := by rw [pow_add, pow_one]; ring
    rw [hr_sub, hrm1_2, Nat.mul_div_cancel_left _ (by norm_num)]
  rw [hr_div2]
  obtain ⟨u, hu_odd, hu_eq⟩ := exists_eq_two_pow_padicValNat_mul_odd (orderOf_zmod_pos hr hcop)
  set t := padicValNat 2 (orderOf (c : ZMod r))
  have ht_le : t ≤ E := padicValNat_orderOf_le hr hcop
  have hu_m : u ∣ m :=
    odd_dvd_of_dvd_two_pow_mul hu_odd
      (dvd_trans ⟨2 ^ t, hu_eq.trans (mul_comm _ _)⟩ (hm_eq ▸ orderOf_zmod_dvd_pred hr hcop))
  have hdvd_iff : orderOf (c : ZMod r) ∣ 2 ^ (E - 1) * m ↔ t ≤ E - 1 := by
    rw [hu_eq]
    constructor
    · intro hd
      exact two_pow_le_of_dvd_two_pow_mul_odd hm_odd (dvd_trans ⟨u, rfl⟩ hd)
    · intro hle
      exact mul_dvd_mul (pow_dvd_pow 2 hle) hu_m
  rw [hdvd_iff]
  omega

/-- Euler's criterion in strict inequality form: for an odd prime `r` and `Nat.Coprime c r`,
`legendreSym r c = 1` iff `v_2(ord_r(c)) < v_2(r - 1)`. -/
theorem legendreSym_eq_one_iff_padicValNat_orderOf_lt {r c : ℕ} [Fact r.Prime]
    (hr_odd : Odd r) (hcop : Nat.Coprime c r) :
    legendreSym r (c : ℤ) = 1 ↔
      padicValNat 2 (orderOf (c : ZMod r)) < padicValNat 2 (r - 1) := by
  have hr : Nat.Prime r := Fact.out
  have hc0 : ((c : ℤ) : ZMod r) ≠ 0 := by
    simpa using zmod_natCast_ne_zero_of_coprime hr hcop
  have hdich := legendreSym.eq_one_or_neg_one (p := r) hc0
  have hneg := legendreSym_eq_neg_one_iff_padicValNat_orderOf hr_odd hcop
  have hle := padicValNat_orderOf_le hr hcop
  constructor
  · intro h1
    have hne_neg : legendreSym r (c : ℤ) ≠ -1 := by rw [h1]; norm_num
    have hne_val : padicValNat 2 (orderOf (c : ZMod r)) ≠ padicValNat 2 (r - 1) :=
      fun heq => hne_neg (hneg.mpr heq)
    omega
  · intro hlt
    have hne_neg : legendreSym r (c : ℤ) ≠ -1 := by
      intro h_eq_neg
      have heq := hneg.mp h_eq_neg
      omega
    exact hdich.resolve_right hne_neg

/-- **Lemma 4 (`lem:k-gen`), parameterized form**:
For odd primes `p, q` with `p - 1 = b * m`, `q - 1 = a * m`, `0 < m`, `n = p * q`,
and `Nat.Coprime c n`, if `IsStrongProbablePrime n c`, then:
1. `v_2(a) = v_2(b) → legendreSym p c = legendreSym q c`;
2. `v_2(b) < v_2(a) → legendreSym q c = 1`;
3. `v_2(a) < v_2(b) → legendreSym p c = 1`. -/
theorem k_gen_legendre_of_sprp {p q a b m n c : ℕ}
    [Fact p.Prime] [Fact q.Prime]
    (hp_odd : Odd p) (hq_odd : Odd q) (hm : 0 < m)
    (hp_eq : p - 1 = b * m) (hq_eq : q - 1 = a * m)
    (hn_eq : n = p * q) (hcop_cn : Nat.Coprime c n)
    (hsprp : IsStrongProbablePrime n c) :
    (padicValNat 2 a = padicValNat 2 b →
      legendreSym p (c : ℤ) = legendreSym q (c : ℤ)) ∧
    (padicValNat 2 b < padicValNat 2 a →
      legendreSym q (c : ℤ) = 1) ∧
    (padicValNat 2 a < padicValNat 2 b →
      legendreSym p (c : ℤ) = 1) := by
  have hp : Nat.Prime p := Fact.out
  have hq : Nat.Prime q := Fact.out
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hb_ne : b ≠ 0 := by
    intro hb0
    rw [hb0, zero_mul] at hp_eq
    have := hp.two_le; omega
  have ha_ne : a ≠ 0 := by
    intro ha0
    rw [ha0, zero_mul] at hq_eq
    have := hq.two_le; omega
  have hvp : padicValNat 2 (p - 1) = padicValNat 2 b + padicValNat 2 m := by
    rw [hp_eq, padicValNat.mul hb_ne hm.ne']
  have hvq : padicValNat 2 (q - 1) = padicValNat 2 a + padicValNat 2 m := by
    rw [hq_eq, padicValNat.mul ha_ne hm.ne']
  have hcop_cp : Nat.Coprime c p := by rw [hn_eq] at hcop_cn; exact hcop_cn.coprime_mul_right_right
  have hcop_cq : Nat.Coprime c q := by rw [hn_eq] at hcop_cn; exact hcop_cn.coprime_mul_left_right
  have heq_ord := semiprime_padicValNat_orderOf_eq_of_sprp hp hq hp_odd hq_odd hn_eq hsprp
  have hle_p := padicValNat_orderOf_le hp hcop_cp
  have hle_q := padicValNat_orderOf_le hq hcop_cq
  refine ⟨?_, ?_, ?_⟩
  · intro hvab
    have hsp_sq : padicValNat 2 (p - 1) = padicValNat 2 (q - 1) := by omega
    by_cases ht : padicValNat 2 (orderOf (c : ZMod p)) = padicValNat 2 (p - 1)
    · have hp_neg : legendreSym p (c : ℤ) = -1 :=
        (legendreSym_eq_neg_one_iff_padicValNat_orderOf hp_odd hcop_cp).mpr ht
      have hq_neg : legendreSym q (c : ℤ) = -1 :=
        (legendreSym_eq_neg_one_iff_padicValNat_orderOf hq_odd hcop_cq).mpr (by omega)
      rw [hp_neg, hq_neg]
    · have hp_pos : legendreSym p (c : ℤ) = 1 :=
        (legendreSym_eq_one_iff_padicValNat_orderOf_lt hp_odd hcop_cp).mpr (by omega)
      have hq_pos : legendreSym q (c : ℤ) = 1 :=
        (legendreSym_eq_one_iff_padicValNat_orderOf_lt hq_odd hcop_cq).mpr (by omega)
      rw [hp_pos, hq_pos]
  · intro hlt
    exact (legendreSym_eq_one_iff_padicValNat_orderOf_lt hq_odd hcop_cq).mpr (by omega)
  · intro hlt
    exact (legendreSym_eq_one_iff_padicValNat_orderOf_lt hp_odd hcop_cp).mpr (by omega)

/-- **Lemma 4 (`lem:k-gen`), direct ratio form `b(q - 1) = a(p - 1)`**:
Matches the verbatim statement of Lemma 4 in `hughes-spsp-psi20.tex`. -/
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
  have hp : Nat.Prime p := Fact.out
  obtain ⟨m, hm_pos, hp_eq, hq_eq⟩ := exists_k_gen_param hp.two_le hb hcop_ab hrel
  exact k_gen_legendre_of_sprp hp_odd hq_odd hm_pos hp_eq hq_eq hn_eq hcop_cn hsprp

/-! ## 7. Sieve Admissible-Residue Count and Exact Jacobsthal `b mod 8` Cell Split -/

private theorem zmod_ringChar_ne_two_of_odd {b : ℕ} [Fact b.Prime] (hb_odd : Odd b) :
    ringChar (ZMod b) ≠ 2 := by
  rw [ZMod.ringChar_zmod_n]
  rintro rfl
  rcases hb_odd with ⟨k, hk⟩
  omega

private theorem zmod_two_ne_zero_of_odd {b : ℕ} [Fact b.Prime] (hb_odd : Odd b) :
    (2 : ZMod b) ≠ 0 := by
  intro h2
  have hdvd : b ∣ 2 := (ZMod.natCast_eq_zero_iff 2 b).mp h2
  have hb : Nat.Prime b := Fact.out
  have hle : b ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  rcases hb_odd with ⟨k, hk⟩
  have := hb.two_le
  omega

/-- For an odd prime `b`, `ZMod b` contains exactly `(b - 1) / 2` nonzero squares. -/
theorem card_nonzero_squares_zmod {b : ℕ} [Fact b.Prime] (hb_odd : Odd b) :
    (Finset.univ.filter (fun y : ZMod b => quadraticChar (ZMod b) y = 1)).card = (b - 1) / 2 := by
  have hchar : ringChar (ZMod b) ≠ 2 := zmod_ringChar_ne_two_of_odd hb_odd
  set Sq := Finset.univ.filter (fun y : ZMod b => quadraticChar (ZMod b) y = 1)
  set Nsq := Finset.univ.filter (fun y : ZMod b => quadraticChar (ZMod b) y = -1)
  have hdisj : Disjoint Sq Nsq := by
    rw [Finset.disjoint_left]
    intro y h1 h2
    simp only [Sq, Nsq, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    omega
  have hunion : Sq ∪ Nsq = (Finset.univ : Finset (ZMod b)).erase 0 := by
    ext y
    simp only [Sq, Nsq, Finset.mem_union, Finset.mem_filter, Finset.mem_erase,
      Finset.mem_univ, true_and, and_true, ne_eq]
    constructor
    · rintro (h1 | h2)
      · rintro rfl; rw [MulChar.map_zero] at h1; norm_num at h1
      · rintro rfl; rw [MulChar.map_zero] at h2; norm_num at h2
    · intro hy0
      exact quadraticChar_dichotomy hy0
  have hcard_sum : Sq.card + Nsq.card = b - 1 := by
    rw [← Finset.card_union_of_disjoint hdisj, hunion,
      Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ, ZMod.card]
  have hsum_zero : (Sq.card : ℤ) - (Nsq.card : ℤ) = 0 := by
    have h0 := quadraticChar_sum_zero (F := ZMod b) hchar
    have hsplit : ∑ y : ZMod b, quadraticChar (ZMod b) y =
        quadraticChar (ZMod b) 0 + ∑ y ∈ Finset.univ.erase 0, quadraticChar (ZMod b) y :=
      (Finset.add_sum_erase Finset.univ (fun y : ZMod b => quadraticChar (ZMod b) y)
        (Finset.mem_univ 0)).symm
    rw [hsplit, MulChar.map_zero, zero_add, ← hunion, Finset.sum_union hdisj] at h0
    have hsq_sum : ∑ y ∈ Sq, quadraticChar (ZMod b) y = (Sq.card : ℤ) := by
      calc
        ∑ y ∈ Sq, quadraticChar (ZMod b) y = ∑ _ ∈ Sq, (1 : ℤ) :=
          Finset.sum_congr rfl fun y hy => (Finset.mem_filter.mp hy).2
        _ = (Sq.card : ℤ) := by simp
    have hnsq_sum : ∑ y ∈ Nsq, quadraticChar (ZMod b) y = -(Nsq.card : ℤ) := by
      calc
        ∑ y ∈ Nsq, quadraticChar (ZMod b) y = ∑ _ ∈ Nsq, (-1 : ℤ) :=
          Finset.sum_congr rfl fun y hy => (Finset.mem_filter.mp hy).2
        _ = -(Nsq.card : ℤ) := by simp
    rw [hsq_sum, hnsq_sum] at h0
    linarith
  have hb_ge3 : 3 ≤ b := by
    have := (Fact.out : b.Prime).two_le
    rcases hb_odd with ⟨k, hk⟩
    omega
  omega

/-- **Sieve admissible-residue count (`ZMod b` form)**:
For an odd prime `b`, the number of nonzero residues `x : ZMod b` for which `2x - 1`
is a nonzero square modulo `b` equals `(b - 1) / 2` if `b ≡ 3 (mod 4)` and `(b - 3) / 2`
if `b ≡ 1 (mod 4)`. -/
theorem sieve_admissible_card {b : ℕ} [Fact b.Prime] (hb_odd : Odd b) :
    (Finset.univ.filter
      (fun x : ZMod b => x ≠ 0 ∧ quadraticChar (ZMod b) (2 * x - 1) = 1)).card =
      if b % 4 = 3 then (b - 1) / 2 else (b - 3) / 2 := by
  have h2 : (2 : ZMod b) ≠ 0 := zmod_two_ne_zero_of_odd hb_odd
  set Sq := Finset.univ.filter (fun y : ZMod b => quadraticChar (ZMod b) y = 1)
  have hbij : (Finset.univ.filter
      (fun x : ZMod b => x ≠ 0 ∧ quadraticChar (ZMod b) (2 * x - 1) = 1)).card =
      (Sq.erase (-1)).card := by
    refine Finset.card_bij (fun x _ => 2 * x - 1) ?_ ?_ ?_
    · intro x hx
      rcases (Finset.mem_filter.mp hx).2 with ⟨hx0, hq1⟩
      rw [Finset.mem_erase]
      refine ⟨?_, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq1⟩⟩
      intro hneg
      have h2x : (2 : ZMod b) * x = 0 := by linear_combination hneg
      exact hx0 ((mul_eq_zero.mp h2x).resolve_left h2)
    · intro x₁ _ x₂ _ heq
      have h2x : (2 : ZMod b) * (x₁ - x₂) = 0 := by linear_combination heq
      exact sub_eq_zero.mp ((mul_eq_zero.mp h2x).resolve_left h2)
    · intro y hy
      rcases Finset.mem_erase.mp hy with ⟨hy_neg1, hy_sq⟩
      let x : ZMod b := (y + 1) * 2⁻¹
      have hx_2x : 2 * x - 1 = y := by
        calc
          2 * ((y + 1) * 2⁻¹) - 1 = (y + 1) * (2 * 2⁻¹) - 1 := by ring
          _ = (y + 1) * 1 - 1 := by rw [mul_inv_cancel₀ h2]
          _ = y := by ring
      have hx0 : x ≠ 0 := by
        intro hz
        rw [hz, mul_zero, zero_sub] at hx_2x
        exact hy_neg1 hx_2x.symm
      refine ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx0, ?_⟩, hx_2x⟩
      rw [hx_2x]
      exact (Finset.mem_filter.mp hy_sq).2
  rw [hbij]
  have hsq_card := card_nonzero_squares_zmod hb_odd
  have hneg1_ne0 : (-1 : ZMod b) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  have hb_ge3 : 3 ≤ b := by
    have := (Fact.out : b.Prime).two_le
    rcases hb_odd with ⟨k, hk⟩
    omega
  split_ifs with hb3
  · have hnot_mem : (-1 : ZMod b) ∉ Sq := by
      intro hmem
      have h1 : quadraticChar (ZMod b) (-1) = 1 := (Finset.mem_filter.mp hmem).2
      have hsq : IsSquare (-1 : ZMod b) := (quadraticChar_one_iff_isSquare hneg1_ne0).mp h1
      exact (ZMod.exists_sq_eq_neg_one_iff.mp hsq) hb3
    rw [Finset.erase_eq_of_notMem hnot_mem, hsq_card]
  · have hmem : (-1 : ZMod b) ∈ Sq := by
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, (quadraticChar_one_iff_isSquare hneg1_ne0).mpr ?_⟩
      exact ZMod.exists_sq_eq_neg_one_iff.mpr hb3
    rw [Finset.card_erase_of_mem hmem, hsq_card]
    rcases hb_odd with ⟨k, hk⟩
    omega

/-- **Sieve admissible-residue count (`ℕ` interval form matching `recompute.py`)**:
For an odd prime `b`, the number of integers `x ∈ [1, b)` with `legendreSym b (2x - 1) = 1`
equals `(b - 1) / 2` if `b ≡ 3 (mod 4)` and `(b - 3) / 2` if `b ≡ 1 (mod 4)`. -/
theorem sieve_admissible_nat_card {b : ℕ} [Fact b.Prime] (hb_odd : Odd b) :
    ((Finset.Ico 1 b).filter
      (fun x : ℕ => legendreSym b (2 * (x : ℤ) - 1) = 1)).card =
      if b % 4 = 3 then (b - 1) / 2 else (b - 3) / 2 := by
  rw [← sieve_admissible_card hb_odd]
  have hb : Nat.Prime b := Fact.out
  have : NeZero b := ⟨hb.ne_zero⟩
  refine Finset.card_bij (fun x _ => (x : ZMod b)) ?_ ?_ ?_
  · intro x hx
    rcases Finset.mem_filter.mp hx with ⟨hico, hleg⟩
    rcases Finset.mem_Ico.mp hico with ⟨h1, hlt⟩
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · intro hz
      have hdvd : b ∣ x := (ZMod.natCast_eq_zero_iff x b).mp hz
      have hle : b ≤ x := Nat.le_of_dvd (by omega) hdvd
      omega
    · change legendreSym b (2 * (x : ℤ) - 1) = 1 at hleg
      unfold legendreSym at hleg
      simpa using hleg
  · intro x₁ hx₁ x₂ hx₂ heq
    have hlt1 : x₁ < b := (Finset.mem_Ico.mp (Finset.mem_filter.mp hx₁).1).2
    have hlt2 : x₂ < b := (Finset.mem_Ico.mp (Finset.mem_filter.mp hx₂).1).2
    have hmod : x₁ % b = x₂ % b := (ZMod.natCast_eq_natCast_iff x₁ x₂ b).mp heq
    rwa [Nat.mod_eq_of_lt hlt1, Nat.mod_eq_of_lt hlt2] at hmod
  · intro z hz
    rcases (Finset.mem_filter.mp hz).2 with ⟨hz0, hq1⟩
    set x := z.val with hx_def
    have hx_lt : x < b := ZMod.val_lt z
    have hx_ge1 : 1 ≤ x := by
      by_contra h0
      have hx0 : x = 0 := by omega
      apply hz0
      have hz_cast : (z : ZMod b) = (x : ZMod b) := (ZMod.natCast_zmod_val z).symm
      rw [hz_cast, hx0, Nat.cast_zero]
    refine ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hx_ge1, hx_lt⟩, ?_⟩,
      ZMod.natCast_zmod_val z⟩
    unfold legendreSym
    have hcast : ((2 * (x : ℤ) - 1 : ℤ) : ZMod b) = 2 * z - 1 := by
      push_cast
      rw [hx_def, ZMod.natCast_zmod_val z]
    rwa [hcast]

/-- Conic character sum `∑ u : ZMod b, χ(u^2 - 1) = -1` for every odd prime `b`. -/
theorem jacobsthal_sum_sq_sub_one {b : ℕ} [Fact b.Prime] (hb_odd : Odd b) :
    (∑ u : ZMod b, quadraticChar (ZMod b) (u ^ 2 - 1)) = -1 := by
  have hchar : ringChar (ZMod b) ≠ 2 := zmod_ringChar_ne_two_of_odd hb_odd
  have h2 : (2 : ZMod b) ≠ 0 := zmod_two_ne_zero_of_odd hb_odd
  set C := ((Finset.univ : Finset (ZMod b)) ×ˢ (Finset.univ : Finset (ZMod b))).filter
    (fun uv : ZMod b × ZMod b => uv.2 ^ 2 = uv.1 ^ 2 - 1)
  have hcard_C : C.card = b - 1 := by
    have hbij : ((Finset.univ : Finset (ZMod b)).erase 0).card = C.card := by
      refine Finset.card_bij
        (fun t _ => ((t + t⁻¹) * 2⁻¹, (t - t⁻¹) * 2⁻¹)) ?_ ?_ ?_
      · intro t ht
        have ht0 : t ≠ 0 := (Finset.mem_erase.mp ht).1
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩, ?_⟩
        have hid : ((t - t⁻¹) * 2⁻¹) ^ 2 =
            ((t + t⁻¹) * 2⁻¹) ^ 2 - (t * t⁻¹) * (2 * 2⁻¹) ^ 2 := by ring
        rw [hid, mul_inv_cancel₀ ht0, mul_inv_cancel₀ h2]
        ring
      · intro t₁ _ t₂ _ heq
        have h1 := congrArg Prod.fst heq
        have h2' := congrArg Prod.snd heq
        dsimp only at h1 h2'
        have hsum1 : ((t₁ + t₁⁻¹) * 2⁻¹) + ((t₁ - t₁⁻¹) * 2⁻¹) = t₁ := by
          calc
            ((t₁ + t₁⁻¹) * 2⁻¹) + ((t₁ - t₁⁻¹) * 2⁻¹) = t₁ * (2 * 2⁻¹) := by ring
            _ = t₁ := by rw [mul_inv_cancel₀ h2, mul_one]
        have hsum2 : ((t₂ + t₂⁻¹) * 2⁻¹) + ((t₂ - t₂⁻¹) * 2⁻¹) = t₂ := by
          calc
            ((t₂ + t₂⁻¹) * 2⁻¹) + ((t₂ - t₂⁻¹) * 2⁻¹) = t₂ * (2 * 2⁻¹) := by ring
            _ = t₂ := by rw [mul_inv_cancel₀ h2, mul_one]
        rw [← hsum1, ← hsum2, h1, h2']
      · intro ⟨u, v⟩ huv
        have heq_sq : v ^ 2 = u ^ 2 - 1 := (Finset.mem_filter.mp huv).2
        have hprod : (u + v) * (u - v) = 1 := by linear_combination -heq_sq
        let t : ZMod b := u + v
        have ht0 : t ≠ 0 := left_ne_zero_of_mul_eq_one hprod
        have ht_inv : t⁻¹ = u - v := inv_eq_of_mul_eq_one_right hprod
        refine ⟨t, Finset.mem_erase.mpr ⟨ht0, Finset.mem_univ t⟩, ?_⟩
        ext
        · dsimp only [t]
          rw [ht_inv]
          calc
            (u + v + (u - v)) * 2⁻¹ = u * (2 * 2⁻¹) := by ring
            _ = u := by rw [mul_inv_cancel₀ h2, mul_one]
        · dsimp only [t]
          rw [ht_inv]
          calc
            (u + v - (u - v)) * 2⁻¹ = v * (2 * 2⁻¹) := by ring
            _ = v := by rw [mul_inv_cancel₀ h2, mul_one]
    rw [← hbij, Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ, ZMod.card]
  have hsum_plus_one :
      (∑ u : ZMod b, (quadraticChar (ZMod b) (u ^ 2 - 1) + 1)) = (C.card : ℤ) := by
    have hper_u : ∀ u : ZMod b,
        quadraticChar (ZMod b) (u ^ 2 - 1) + 1 =
          ((Finset.univ.filter (fun v : ZMod b => v ^ 2 = u ^ 2 - 1)).card : ℤ) := by
      intro u
      have hq := (quadraticChar_card_sqrts hchar (u ^ 2 - 1)).symm
      have hset : {v : ZMod b | v ^ 2 = u ^ 2 - 1}.toFinset =
          Finset.univ.filter (fun v : ZMod b => v ^ 2 = u ^ 2 - 1) := by
        ext v; simp
      rwa [hset] at hq
    simp_rw [hper_u]
    norm_cast
    have hprod_eq : C.card =
        ∑ u : ZMod b, (Finset.univ.filter (fun v : ZMod b => v ^ 2 = u ^ 2 - 1)).card := by
      let fib : ZMod b → Finset (ZMod b × ZMod b) := fun u =>
        ({u} : Finset (ZMod b)) ×ˢ (Finset.univ.filter (fun v : ZMod b => v ^ 2 = u ^ 2 - 1))
      have hc_bi : C = (Finset.univ : Finset (ZMod b)).biUnion fib := by
        ext ⟨u, v⟩
        simp only [C, fib, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and,
          Finset.mem_biUnion, Finset.mem_singleton]
        exact ⟨fun h => ⟨u, rfl, h⟩, fun ⟨a, ha, hv⟩ => ha ▸ hv⟩
      have hdisj : Set.PairwiseDisjoint (↑(Finset.univ : Finset (ZMod b)) : Set (ZMod b)) fib := by
        intro u₁ _ u₂ _ hne
        rw [Function.onFun, Finset.disjoint_left]
        intro ⟨x, y⟩ h1 h2
        simp only [fib, Finset.mem_product, Finset.mem_singleton] at h1 h2
        exact hne (h1.1.symm.trans h2.1)
      rw [hc_bi, Finset.card_biUnion hdisj]
      refine Finset.sum_congr rfl fun u _ => ?_
      simp [fib]
    exact hprod_eq.symm
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, ZMod.card,
    nsmul_eq_mul, mul_one, hcard_C] at hsum_plus_one
  have hb_ge1 : 1 ≤ b := (Fact.out : b.Prime).pos
  omega

/-- **Jacobsthal correlation sum**: For every odd prime `b`,
`∑ x : ZMod b, χ(x) * χ(2x - 1) = -legendreSym b 2`. -/
theorem jacobsthal_sum_two_mul_sq_sub {b : ℕ} [Fact b.Prime] (hb_odd : Odd b) :
    (∑ x : ZMod b, quadraticChar (ZMod b) x * quadraticChar (ZMod b) (2 * x - 1)) =
      -legendreSym b 2 := by
  have h2 : (2 : ZMod b) ≠ 0 := zmod_two_ne_zero_of_odd hb_odd
  have h4 : (4 : ZMod b) ≠ 0 := by
    have h4eq : (4 : ZMod b) = 2 * 2 := by norm_num
    rw [h4eq]
    exact mul_ne_zero h2 h2
  have hchi8 : quadraticChar (ZMod b) 8 = legendreSym b 2 := by
    have h8 : (8 : ZMod b) = 2 * 2 ^ 2 := by norm_num
    rw [h8, map_mul, quadraticChar_sq_one' h2, mul_one]
    simp [legendreSym]
  have hleg2_sq : legendreSym b 2 * legendreSym b 2 = 1 := by
    have h2z : ((2 : ℤ) : ZMod b) ≠ 0 := by simpa using h2
    rcases legendreSym.eq_one_or_neg_one (p := b) h2z with h | h <;> simp [h]
  have hmul_sum :
      legendreSym b 2 *
        (∑ x : ZMod b, quadraticChar (ZMod b) x * quadraticChar (ZMod b) (2 * x - 1)) = -1 := by
    rw [← hchi8, Finset.mul_sum]
    have hterm : ∀ x : ZMod b,
        quadraticChar (ZMod b) 8 *
          (quadraticChar (ZMod b) x * quadraticChar (ZMod b) (2 * x - 1)) =
          quadraticChar (ZMod b) ((4 * x - 1) ^ 2 - 1) := by
      intro x
      rw [← map_mul, ← map_mul]
      congr 1
      ring
    simp_rw [hterm]
    let e : ZMod b ≃ ZMod b :=
      { toFun := fun x => 4 * x - 1
        invFun := fun u => (u + 1) * 4⁻¹
        left_inv := fun x => by
          calc
            (4 * x - 1 + 1) * 4⁻¹ = x * (4 * 4⁻¹) := by ring
            _ = x := by rw [mul_inv_cancel₀ h4, mul_one]
        right_inv := fun u => by
          calc
            4 * ((u + 1) * 4⁻¹) - 1 = (u + 1) * (4 * 4⁻¹) - 1 := by ring
            _ = u := by rw [mul_inv_cancel₀ h4]; ring }
    have hbij_sum :
        (∑ x : ZMod b, quadraticChar (ZMod b) ((4 * x - 1) ^ 2 - 1)) =
          ∑ u : ZMod b, quadraticChar (ZMod b) (u ^ 2 - 1) :=
      Fintype.sum_equiv e _ _ (fun _ => rfl)
    rw [hbij_sum]
    exact jacobsthal_sum_sq_sub_one hb_odd
  calc
    (∑ x : ZMod b, quadraticChar (ZMod b) x * quadraticChar (ZMod b) (2 * x - 1))
        = (legendreSym b 2 * legendreSym b 2) *
            (∑ x : ZMod b, quadraticChar (ZMod b) x * quadraticChar (ZMod b) (2 * x - 1)) := by
          rw [hleg2_sq, one_mul]
    _ = legendreSym b 2 *
          (legendreSym b 2 *
            (∑ x : ZMod b, quadraticChar (ZMod b) x * quadraticChar (ZMod b) (2 * x - 1))) := by
          ring
    _ = -legendreSym b 2 := by rw [hmul_sum]; ring

/-- **Exact `b mod 8` quadratic cell split for `K2` prime pairs**:
Among the `b - 2` prime-pair-admissible residues `x ∈ ZMod b \ {0, 2⁻¹}` for an odd prime `b`,
let `N_{-+}` count residues with `χ(x) = -1, χ(2x - 1) = 1` and `N_{++}` count residues with
`χ(x) = 1, χ(2x - 1) = 1`. Then:
- `4 * N_{-+} = b - 2 - legendreSym b (-1) + 2 * legendreSym b 2`,
- `4 * N_{++} = b - 2 - legendreSym b (-1) - 2 * legendreSym b 2`. -/
theorem k2_quadratic_cell_counts {b : ℕ} [Fact b.Prime] (hb_odd : Odd b) :
    (4 * ((Finset.univ.filter
        (fun x : ZMod b =>
          quadraticChar (ZMod b) x = -1 ∧ quadraticChar (ZMod b) (2 * x - 1) = 1)).card : ℤ) =
      (b : ℤ) - 2 - legendreSym b (-1) + 2 * legendreSym b 2) ∧
    (4 * ((Finset.univ.filter
        (fun x : ZMod b =>
          quadraticChar (ZMod b) x = 1 ∧ quadraticChar (ZMod b) (2 * x - 1) = 1)).card : ℤ) =
      (b : ℤ) - 2 - legendreSym b (-1) - 2 * legendreSym b 2) := by
  have hchar : ringChar (ZMod b) ≠ 2 := zmod_ringChar_ne_two_of_odd hb_odd
  have h2 : (2 : ZMod b) ≠ 0 := zmod_two_ne_zero_of_odd hb_odd
  set Cmp := Finset.univ.filter
    (fun x : ZMod b => quadraticChar (ZMod b) x = -1 ∧ quadraticChar (ZMod b) (2 * x - 1) = 1)
  set Cpp := Finset.univ.filter
    (fun x : ZMod b => quadraticChar (ZMod b) x = 1 ∧ quadraticChar (ZMod b) (2 * x - 1) = 1)
  set Adm := ((Finset.univ : Finset (ZMod b)).erase 0).erase (2⁻¹ : ZMod b)
  have hhalf_ne0 : (2⁻¹ : ZMod b) ≠ 0 := inv_ne_zero h2
  have hadm_card : Adm.card = b - 2 := by
    have hmem : (2⁻¹ : ZMod b) ∈ (Finset.univ : Finset (ZMod b)).erase 0 :=
      Finset.mem_erase.mpr ⟨hhalf_ne0, Finset.mem_univ _⟩
    rw [Finset.card_erase_of_mem hmem, Finset.card_erase_of_mem (Finset.mem_univ 0),
      Finset.card_univ, ZMod.card]
    omega
  have hchi_dich_adm : ∀ x ∈ Adm,
      (quadraticChar (ZMod b) x = 1 ∨ quadraticChar (ZMod b) x = -1) ∧
      (quadraticChar (ZMod b) (2 * x - 1) = 1 ∨ quadraticChar (ZMod b) (2 * x - 1) = -1) := by
    intro x hx
    have hx_ne2 : x ≠ 2⁻¹ := (Finset.mem_erase.mp hx).1
    have hx_ne0 : x ≠ 0 := (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).1
    have h2x_ne0 : 2 * x - 1 ≠ 0 := by
      intro hz
      apply hx_ne2
      have h2x : 2 * x = 1 := sub_eq_zero.mp hz
      calc
        x = x * (2 * 2⁻¹) := by rw [mul_inv_cancel₀ h2, mul_one]
        _ = (2 * x) * 2⁻¹ := by ring
        _ = 2⁻¹ := by rw [h2x, one_mul]
    exact ⟨quadraticChar_dichotomy hx_ne0, quadraticChar_dichotomy h2x_ne0⟩
  have hcmp_sub : Cmp ⊆ Adm := by
    intro x hx
    rcases (Finset.mem_filter.mp hx).2 with ⟨hx1, hx2⟩
    rw [Finset.mem_erase, Finset.mem_erase]
    refine ⟨?_, ?_, Finset.mem_univ x⟩
    · intro rfl; rw [mul_inv_cancel₀ h2, sub_self, MulChar.map_zero] at hx2; omega
    · intro rfl; rw [MulChar.map_zero] at hx1; omega
  have hcpp_sub : Cpp ⊆ Adm := by
    intro x hx
    rcases (Finset.mem_filter.mp hx).2 with ⟨hx1, hx2⟩
    rw [Finset.mem_erase, Finset.mem_erase]
    refine ⟨?_, ?_, Finset.mem_univ x⟩
    · intro rfl; rw [mul_inv_cancel₀ h2, sub_self, MulChar.map_zero] at hx2; omega
    · intro rfl; rw [MulChar.map_zero] at hx1; omega
  have hind_mp : ∀ x ∈ Adm,
      (1 - quadraticChar (ZMod b) x) * (1 + quadraticChar (ZMod b) (2 * x - 1)) =
        if x ∈ Cmp then 4 else 0 := by
    intro x hx
    rcases hchi_dich_adm x hx with ⟨hx1 | hx1, hx2 | hx2⟩ <;>
      · simp only [Cmp, Finset.mem_filter, Finset.mem_univ, true_and, hx1, hx2]
        norm_num
  have hind_pp : ∀ x ∈ Adm,
      (1 + quadraticChar (ZMod b) x) * (1 + quadraticChar (ZMod b) (2 * x - 1)) =
        if x ∈ Cpp then 4 else 0 := by
    intro x hx
    rcases hchi_dich_adm x hx with ⟨hx1 | hx1, hx2 | hx2⟩ <;>
      · simp only [Cpp, Finset.mem_filter, Finset.mem_univ, true_and, hx1, hx2]
        norm_num
  have hsum_mp :
      ∑ x ∈ Adm, (1 - quadraticChar (ZMod b) x) * (1 + quadraticChar (ZMod b) (2 * x - 1)) =
        4 * (Cmp.card : ℤ) := by
    rw [Finset.sum_congr rfl hind_mp, Finset.sum_ite_mem, Finset.inter_eq_right.mpr hcmp_sub]
    simp [mul_comm]
  have hsum_pp :
      ∑ x ∈ Adm, (1 + quadraticChar (ZMod b) x) * (1 + quadraticChar (ZMod b) (2 * x - 1)) =
        4 * (Cpp.card : ℤ) := by
    rw [Finset.sum_congr rfl hind_pp, Finset.sum_ite_mem, Finset.inter_eq_right.mpr hcpp_sub]
    simp [mul_comm]
  have hsum_1 : (∑ _ ∈ Adm, (1 : ℤ)) = (b : ℤ) - 2 := by
    rw [Finset.sum_const, nsmul_eq_mul, mul_one, hadm_card]
    have hb_ge3 : 3 ≤ b := by
      have := (Fact.out : b.Prime).two_le
      rcases hb_odd with ⟨k, hk⟩; omega
    omega
  have herase_sum : ∀ (f : ZMod b → ℤ),
      ∑ x ∈ Adm, f x = (∑ x : ZMod b, f x) - f 0 - f (2⁻¹) := by
    intro f
    have hmem2 : (2⁻¹ : ZMod b) ∈ (Finset.univ : Finset (ZMod b)).erase 0 :=
      Finset.mem_erase.mpr ⟨hhalf_ne0, Finset.mem_univ _⟩
    have h1 := Finset.add_sum_erase ((Finset.univ : Finset (ZMod b)).erase 0) f hmem2
    have h2' := Finset.add_sum_erase (Finset.univ : Finset (ZMod b)) f (Finset.mem_univ 0)
    change f (2⁻¹) + ∑ x ∈ Adm, f x = ∑ x ∈ Finset.univ.erase 0, f x at h1
    linarith
  have hchi_inv2 : quadraticChar (ZMod b) (2⁻¹ : ZMod b) = legendreSym b 2 := by
    have hprod : (2⁻¹ : ZMod b) = 2 * (2⁻¹) ^ 2 := by
      calc
        (2⁻¹ : ZMod b) = (2 * 2⁻¹) * 2⁻¹ := by rw [mul_inv_cancel₀ h2, one_mul]
        _ = 2 * (2⁻¹) ^ 2 := by ring
    rw [hprod, map_mul, quadraticChar_sq_one' hhalf_ne0, mul_one]
    simp [legendreSym]
  have hsum_x : (∑ x ∈ Adm, quadraticChar (ZMod b) x) = -legendreSym b 2 := by
    rw [herase_sum, quadraticChar_sum_zero hchar, MulChar.map_zero, hchi_inv2]
    ring
  have hsum_2x : (∑ x ∈ Adm, quadraticChar (ZMod b) (2 * x - 1)) = -legendreSym b (-1) := by
    rw [herase_sum]
    let e2 : ZMod b ≃ ZMod b :=
      { toFun := fun x => 2 * x - 1
        invFun := fun y => (y + 1) * 2⁻¹
        left_inv := fun x => by
          calc
            (2 * x - 1 + 1) * 2⁻¹ = x * (2 * 2⁻¹) := by ring
            _ = x := by rw [mul_inv_cancel₀ h2, mul_one]
        right_inv := fun y => by
          calc
            2 * ((y + 1) * 2⁻¹) - 1 = (y + 1) * (2 * 2⁻¹) - 1 := by ring
            _ = y := by rw [mul_inv_cancel₀ h2]; ring }
    have hfull : (∑ x : ZMod b, quadraticChar (ZMod b) (2 * x - 1)) =
        ∑ y : ZMod b, quadraticChar (ZMod b) y :=
      Fintype.sum_equiv e2 _ _ (fun _ => rfl)
    have h_at0 : quadraticChar (ZMod b) (2 * (0 : ZMod b) - 1) = legendreSym b (-1) := by
      simp [legendreSym]
    have h_athalf : quadraticChar (ZMod b) (2 * (2⁻¹ : ZMod b) - 1) = 0 := by
      rw [mul_inv_cancel₀ h2, sub_self, MulChar.map_zero]
    rw [hfull, quadraticChar_sum_zero hchar, h_at0, h_athalf]
    ring
  have hsum_prod :
      (∑ x ∈ Adm, quadraticChar (ZMod b) x * quadraticChar (ZMod b) (2 * x - 1)) =
        -legendreSym b 2 := by
    rw [herase_sum, jacobsthal_sum_two_mul_sq_sub hb_odd]
    have h0_term : quadraticChar (ZMod b) 0 * quadraticChar (ZMod b) (2 * 0 - 1) = 0 := by
      simp
    have hhalf_term :
        quadraticChar (ZMod b) (2⁻¹) * quadraticChar (ZMod b) (2 * (2⁻¹ : ZMod b) - 1) = 0 := by
      rw [mul_inv_cancel₀ h2, sub_self, MulChar.map_zero, mul_zero]
    rw [h0_term, hhalf_term]
    ring
  have hexpand_mp :
      (∑ x ∈ Adm, (1 - quadraticChar (ZMod b) x) * (1 + quadraticChar (ZMod b) (2 * x - 1))) =
        (∑ _ ∈ Adm, (1 : ℤ)) - (∑ x ∈ Adm, quadraticChar (ZMod b) x) +
          (∑ x ∈ Adm, quadraticChar (ZMod b) (2 * x - 1)) -
          (∑ x ∈ Adm, quadraticChar (ZMod b) x * quadraticChar (ZMod b) (2 * x - 1)) := by
    simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => by ring
  have hexpand_pp :
      (∑ x ∈ Adm, (1 + quadraticChar (ZMod b) x) * (1 + quadraticChar (ZMod b) (2 * x - 1))) =
        (∑ _ ∈ Adm, (1 : ℤ)) + (∑ x ∈ Adm, quadraticChar (ZMod b) x) +
          (∑ x ∈ Adm, quadraticChar (ZMod b) (2 * x - 1)) +
          (∑ x ∈ Adm, quadraticChar (ZMod b) x * quadraticChar (ZMod b) (2 * x - 1)) := by
    simp only [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => by ring
  rw [hexpand_mp, hsum_1, hsum_x, hsum_2x, hsum_prod] at hsum_mp
  rw [hexpand_pp, hsum_1, hsum_x, hsum_2x, hsum_prod] at hsum_pp
  exact ⟨by linarith, by linarith⟩

/-- Combined Theorem 2: Fermat Legendre criterion and Miller–Rabin 2-adic order/level
criteria for any odd prime `p` with `n = p(2p - 1)` in `K2` and `gcd(b, n) = 1`. -/
theorem k2_fermat_and_sprp_criteria {n p b : ℕ} (hk2 : IsK2Number n p) (hp_odd : Odd p)
    [Fact (Nat.Prime (2 * p - 1))] (hcop : Nat.Coprime b n) :
    (b ^ (n - 1) ≡ 1 [MOD n] ↔ legendreSym (2 * p - 1) (b : ℤ) = 1) ∧
    (IsStrongProbablePrime n b ↔
      padicValNat 2 (orderOf (b : ZMod p)) =
        padicValNat 2 (orderOf (b : ZMod (2 * p - 1)))) ∧
    (IsStrongProbablePrime n b ↔ twoPowLevel (2 * p - 1) b = twoPowLevel p b + 1) :=
  ⟨k2_fermat_iff_legendre hk2 hcop,
   k2_sprp_iff_two_adic_order hk2 hp_odd hcop,
   k2_sprp_iff_level hk2 hp_odd hcop⟩

/-- Combined Proposition 3: exact strong-liar fraction `(1 + 2 * 4^(-e)) / 6`, base-2
exclusion at `p % 4 = 3` (`share = 1/4`), congruence constraints and `≤ 3/16` cap when
passing base `2`, and equality `3/16` at `e = 2`. -/
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
  ⟨k2_strongLiar_share_rat hk2 hp_odd,
   fun hp3 => ⟨k2_strongLiar_share_e1 hk2 hp3, k2_not_sprp_two_of_mod_four_eq_three hk2 hp3⟩,
   fun h2 =>
     let hm := k2_mod_of_sprp_two hk2 h2
     ⟨hm.1, hm.2.1, hm.2.2, k2_strongLiar_share_le_of_sprp_two hk2 h2⟩,
   fun he2 => k2_strongLiar_share_e2 hk2 he2⟩

/-- Exact first-wheel modulus (`4 * ∏_{3 ≤ b ≤ 31} b = 401120980260`) and product of the
ten local counts (`∏_{3 ≤ b ≤ 31} A(b) = 10135125`); the paper's written Chinese remainder
theorem argument identifies that product with the number of simultaneous admissible
classes. -/
theorem first_wheel_exact :
    4 * ([3, 5, 7, 11, 13, 17, 19, 23, 29, 31] : List ℕ).prod = 401120980260 ∧
    (([3, 5, 7, 11, 13, 17, 19, 23, 29, 31] : List ℕ).map
      (fun b => if b % 4 = 3 then (b - 1) / 2 else (b - 3) / 2)).prod = 10135125 := by
  decide

/-- Combined Proposition 4: general odd-prime admissible residue count `A(b)` together
with the exact first-wheel modulus and the product of the ten local counts. -/
theorem sieve_admissible_and_wheel {b : ℕ} [Fact b.Prime] (hb_odd : Odd b) :
    (Finset.univ.filter
      (fun x : ZMod b => x ≠ 0 ∧ quadraticChar (ZMod b) (2 * x - 1) = 1)).card =
      (if b % 4 = 3 then (b - 1) / 2 else (b - 3) / 2) ∧
    4 * ([3, 5, 7, 11, 13, 17, 19, 23, 29, 31] : List ℕ).prod = 401120980260 ∧
    (([3, 5, 7, 11, 13, 17, 19, 23, 29, 31] : List ℕ).map
      (fun q => if q % 4 = 3 then (q - 1) / 2 else (q - 3) / 2)).prod = 10135125 :=
  ⟨sieve_admissible_card hb_odd, first_wheel_exact.1, first_wheel_exact.2⟩

/-- Combined Theorem 5: exact Jacobsthal correlation sum `-(2/b)` and exact `b mod 8`
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
      (b : ℤ) - 2 - legendreSym b (-1) - 2 * legendreSym b 2) :=
  let hc := k2_quadratic_cell_counts hb_odd
  ⟨jacobsthal_sum_two_mul_sq_sub hb_odd, hc.1, hc.2⟩

end SpspPsi20

end
