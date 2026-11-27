/-
Copyright (c) 2026 Tyler B. Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tyler B. Hughes
-/
module

public import SpspPsi20

/-!
# Axiom Verification Audit for `SpspPsi20`

Prints the Lean 4 kernel axioms used by every formalized theorem, lemma,
proposition, and corollary in `SpspPsi20`. A clean audit must show ONLY
Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`) — NEVER
`sorryAx`, `Lean.ofReduceBool`, `Lean.trustCompiler`, or any custom axiom.
-/

-- Core definitions and structural lemmas (Defs.lean)
#print axioms SpspPsi20.odd_two_pow_mul_unique
#print axioms SpspPsi20.exists_unique_two_pow_mul_odd
#print axioms SpspPsi20.isStrongProbablePrime_iff_of_decomp
#print axioms SpspPsi20.sq_sub_one_modEq_one
#print axioms SpspPsi20.isStrongProbablePrime_implies_fermat
#print axioms SpspPsi20.isFirstKPrimesStrongPseudoprime_mono
#print axioms SpspPsi20.psi_le_of_spsp
#print axioms SpspPsi20.psi_mono
#print axioms SpspPsi20.isK2Number_not_prime

-- Algebraic criteria, liar densities, and sieve laws (Criteria.lean)
#print axioms SpspPsi20.exists_eq_two_pow_padicValNat_mul_odd
#print axioms SpspPsi20.padicValNat_two_pow_mul_odd
#print axioms SpspPsi20.twoPowLevel_le
#print axioms SpspPsi20.le_twoPowLevel_of_modEq_one
#print axioms SpspPsi20.twoPowLevel_modEq_one
#print axioms SpspPsi20.padicValNat_orderOf_le
#print axioms SpspPsi20.twoPowLevel_add_padicValNat_orderOf
#print axioms SpspPsi20.twoPowLevel_eq_sub
#print axioms SpspPsi20.semiprime_padicValNat_orderOf_eq_of_sprp
#print axioms SpspPsi20.k2_coprime_factors
#print axioms SpspPsi20.k2_pred_eq
#print axioms SpspPsi20.k2_two_adic_decomp
#print axioms SpspPsi20.k2_padicValNat_pred
#print axioms SpspPsi20.k2_fermat_iff_euler
#print axioms SpspPsi20.k2_fermat_iff_legendre
#print axioms SpspPsi20.k2_sprp_iff_two_adic_order
#print axioms SpspPsi20.k2_sprp_iff_level
#print axioms SpspPsi20.k2_not_sprp_two_of_mod_four_eq_three
#print axioms SpspPsi20.k2_mod_of_sprp_two
#print axioms SpspPsi20.cyclic_card_pow_eq_one
#print axioms SpspPsi20.zmod_units_card_two_adic_order_zero
#print axioms SpspPsi20.zmod_units_card_two_adic_order_succ
#print axioms SpspPsi20.k2_strongLiarCount_mul_three
#print axioms SpspPsi20.k2_strongLiarCount_eq
#print axioms SpspPsi20.k2_strongLiar_share_rat
#print axioms SpspPsi20.k2_strongLiar_share_e1
#print axioms SpspPsi20.k2_strongLiar_share_e2
#print axioms SpspPsi20.k2_strongLiar_share_le_of_sprp_two
#print axioms SpspPsi20.exists_k_gen_param
#print axioms SpspPsi20.legendreSym_eq_neg_one_iff_padicValNat_orderOf
#print axioms SpspPsi20.legendreSym_eq_one_iff_padicValNat_orderOf_lt
#print axioms SpspPsi20.k_gen_legendre_of_sprp
#print axioms SpspPsi20.k_gen_legendre_of_ratio
#print axioms SpspPsi20.card_nonzero_squares_zmod
#print axioms SpspPsi20.sieve_admissible_card
#print axioms SpspPsi20.sieve_admissible_nat_card
#print axioms SpspPsi20.jacobsthal_sum_sq_sub_one
#print axioms SpspPsi20.jacobsthal_sum_two_mul_sq_sub
#print axioms SpspPsi20.k2_quadratic_cell_counts

-- Verified modular exponentiation, Pratt soundness, and first 21 primes (Pratt.lean)
#print axioms SpspPsi20.modPowAux_eq
#print axioms SpspPsi20.modPowFuel_eq
#print axioms SpspPsi20.modPowFuel_modEq
#print axioms SpspPsi20.lt_two_pow_log2_succ
#print axioms SpspPsi20.modPow_eq
#print axioms SpspPsi20.modPow_modEq
#print axioms SpspPsi20.zmod_pow_eq_one_iff
#print axioms SpspPsi20.mem_of_prime_dvd_list_prod
#print axioms SpspPsi20.prime_of_pratt
#print axioms SpspPsi20.sprpCheck_eq_true_iff
#print axioms SpspPsi20.countPrimes_eq_count
#print axioms SpspPsi20.nth_prime_of_countPrimes
#print axioms SpspPsi20.nth_prime_table
#print axioms SpspPsi20.nth_prime_20
#print axioms SpspPsi20.forall_nth_prime_sprp_of_all

-- Two explicit 37-digit 20-base strong pseudoprimes and bounds (Witnesses.lean)
#print axioms SpspPsi20.n₁_eq
#print axioms SpspPsi20.n₂_eq
#print axioms SpspPsi20.n₁_lt_n₂
#print axioms SpspPsi20.n₁_in_band
#print axioms SpspPsi20.n₂_in_band
#print axioms SpspPsi20.p₁_prime
#print axioms SpspPsi20.q₁_prime
#print axioms SpspPsi20.n₁_isK2
#print axioms SpspPsi20.n₁_not_prime
#print axioms SpspPsi20.p₂_prime
#print axioms SpspPsi20.q₂_prime
#print axioms SpspPsi20.n₂_isK2
#print axioms SpspPsi20.n₂_not_prime
#print axioms SpspPsi20.n₁_spsp_20
#print axioms SpspPsi20.n₁_fails_73
#print axioms SpspPsi20.n₁_not_spsp_21
#print axioms SpspPsi20.n₂_spsp_20
#print axioms SpspPsi20.n₂_fails_73
#print axioms SpspPsi20.n₂_not_spsp_21
#print axioms SpspPsi20.psi_20_le_n₁
#print axioms SpspPsi20.psi_20_le_n₂
#print axioms SpspPsi20.psi_le_n₁_of_le_20

-- Hand cases, false variants, and Draft 4 1-to-1 paper-theorem bundles
#print axioms SpspPsi20.spsp_2047_base2
#print axioms SpspPsi20.not_spsp_2047_base3
#print axioms SpspPsi20.k2_15_not_spsp2
#print axioms SpspPsi20.n₁_plus2_fails_2
#print axioms SpspPsi20.n₂_plus2_fails_2
#print axioms SpspPsi20.n₁_bit_bounds
#print axioms SpspPsi20.n₂_bit_bounds
#print axioms SpspPsi20.n₁_fermat_73
#print axioms SpspPsi20.n₂_fermat_73
#print axioms SpspPsi20.main_two_witnesses
#print axioms SpspPsi20.k2_fermat_and_sprp_criteria
#print axioms SpspPsi20.k2_strongLiar_share_and_base2_cap
#print axioms SpspPsi20.first_wheel_exact
#print axioms SpspPsi20.sieve_admissible_and_wheel
#print axioms SpspPsi20.k2_jacobsthal_and_cells
