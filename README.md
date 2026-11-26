# Two 37-Digit 20-Base Strong Pseudoprimes (`ψ_20 ≤ n₁ < 2^121`), Order Criteria, and Exact Sieve Laws (Lean 4)

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24490765.svg)](https://doi.org/10.5281/zenodo.24490765)

**Author:** Tyler B. Hughes  
**Disclosure:** Generated and mechanically checked by AI research agents built and directed by Tyler B. Hughes. No human mathematician has yet refereed the proof.  
**Companion page & manuscript:** https://mathdiscoveries.org/results/spsp-psi20

## Summary

This repository is a self-contained Lean 4 (`v4.35.0` + Mathlib `v4.35.0`) formalization of **6 of 8 main claims** of the companion paper (75%; Theorems 1, 2 and 5 and Propositions 3, 4 and 6, all compared in full by the Palomar check; Propositions 7 and 8 are external sieve computations, by certificate only; Conjecture 9 is open and not counted; abstract claims: 6 of 7 compared in Lean, 86%, and 1 by certificate only; 100 verified declarations, `0 sorry`, `0 native_decide`, standard axioms `[propext, Quot.sound, Classical.choice]` only):

| Theorem in `Challenge.lean` | Manuscript claim | Status |
|---|---|---|
| `SpspPsi20Challenge.main_two_witnesses` | **Theorem 1:** Both 37-digit `K2` witnesses `n₁` (121 bits) and `n₂` (123 bits), all 4 Pratt primality proofs, 20-base SPRP (`2..71` via `Nat.nth Nat.Prime`), base-73 strong failure + Fermat pass, and `ψ_20 ≤ n₁ < 2^121` | Pure Lean 4 kernel |
| `SpspPsi20Challenge.psi_20_le_n₁` | Standalone upper bound `ψ_20 ≤ 2481162833436289154832260656117034821` | Pure Lean 4 kernel |
| `SpspPsi20Challenge.k2_fermat_and_sprp_criteria` | **Theorem 2:** `K2` Fermat Legendre criterion and Miller-Rabin 2-adic order/level criteria | Pure Lean 4 kernel |
| `SpspPsi20Challenge.k2_strongLiar_share_and_base2_cap` | **Proposition 3:** Exact strong-liar fraction `(1 + 2·4^(-e))/6`, `p ≡ 3 (mod 4)` base-2 exclusion, and `≤ 3/16` cap | Pure Lean 4 kernel |
| `SpspPsi20Challenge.sieve_admissible_and_wheel` | **Proposition 4:** Exact sieve admissible count `A(b)` and 10-prime wheel (`10,135,125` classes mod `401,120,980,260`) | Pure Lean 4 kernel |
| `SpspPsi20Challenge.k2_jacobsthal_and_cells` | **Theorem 5:** Exact Jacobsthal sum `-(2/b)` and exact `b mod 8` cell identities `4 N_{-+}`, `4 N_{++}` | Pure Lean 4 kernel |
| `SpspPsi20Challenge.k_gen_legendre_of_ratio` | **Proposition 6:** General `K_{a/b}` 2-adic Legendre obstruction | Pure Lean 4 kernel |
| `SpspPsi20Challenge.nth_prime_20` | Grounding witness `Nat.nth Nat.Prime 20 = 73` | Pure Lean 4 kernel |

Theorem 2 formalizes the single-base, two-prime case of [Gerhard Jaeschke's
order-signature criterion](https://doi.org/10.1090/S0025-5718-1993-1192971-8)
(Proposition 1) in the `K2` setting. The library also gives an Euler-criterion
form of Jaeschke's `K2` Fermat criterion (Proposition 4 and its base-2 remark).
Proposition 3 uses the resulting base-2 congruence restriction to bound the
strong-liar fraction.

The companion manuscript by Tyler B. Hughes presents this project's two
37-digit witnesses and their upper bound, the exact strong-liar fraction and
base-2 cap, the wheel count, the Jacobsthal cell identities, and the
general-ratio Legendre obstruction.

## Scope & Divergences

- Two external exhaustive C-sieve searches in the companion manuscript, **Proposition 7** (1,024-shard GMP C sieve over `1.53 × 10^18` integers in `(10^36, 10^37]`) and **Proposition 8** (7-ratio C sweep over `1.49 × 10^10` candidates), are outside Lean's kernel and are not included in `Challenge.lean`.
- Zhang's minimality conjecture (`ψ_t = ψ'_t` for `t ≥ 12`, including whether `ψ_20 = n₁`) remains open.

## Verification

```sh
lake build SpspPsi20 Challenge Solution
lake env lean SpspPsi20/Verify.lean
lake comparator --paranoid --inadvisably-no-sandbox
```
