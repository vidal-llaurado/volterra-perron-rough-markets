/-
  Main entry point for the formalization of
  "A Rough Theory of Markets: Latent Contagion, Market Phases, and Market-Variance Risk"
  by J. Vidal Llauradó (DOI: 10.2139/ssrn.6616121)

  This file imports all modules of the Lean 4 formalization.
-/
import RequestProject.Defs
import RequestProject.Admissibility
import RequestProject.PerronDecomposition
import RequestProject.Synchronization
import RequestProject.Compression
import RequestProject.PhaseStructure
import RequestProject.RLScaling

/-!
# Formalized Results

This project formalizes the core definitions and theorems of the paper
"A Rough Theory of Markets" in Lean 4 with Mathlib. The formalization covers
the logical chain from definitions through roughness necessity, synchronization,
and compression/hedging bounds. All results compile without `sorry`.

## Core Definitions (`Defs.lean`)
- `VolterraMarket N`: N-asset directed Volterra market structure (Assumption 2.1)
- `activeEdges`: Active edge set E_act = {(i,j) : w_i β_{ij} ≠ 0} (Definition 3.5)
- `dominantEdges`: Dominant edge set E* (Definition 3.5)
- `H_star`: Dominant exponent H* = min_{(i,j) ∈ E_act} H_{ij}
- `isAdmissible`: Projected-minimax admissibility (Definition 3.4)
- `admissibleEdges`: Admissible edge set E_adm
- `H_adm`: Admissible exponent
- `noncancelling`: Noncancelling aggregation (Assumption 3.4)
- `ContagionPhase`: Phase classification inductive type (Definition 7.7)

## Admissibility and Roughness Necessity (`Admissibility.lean`)
- `smooth_failure`: Lemma 3.3 — smooth channels (H ≥ 1/2) are not admissible
- `admissibility_characterization`: Proposition 3.6 — admissible ↔ H < 1/2
- `admissibility_nonvacuous`: Corollary 3.7 — admissible class is nonempty
- `admissibility_forces_roughness`: Lemma 4.1 — admissibility forces H < 1/2
- `dominantEdges_nonempty`: Dominant edges are nonempty when active edges are
- `H_adm_eq_H_star`: H_adm = H* under admissible dominant asymmetry
- `market_roughness_necessity`: **Theorem 5.1** — H_M < 1/2 under admissible dominance
- `market_roughness_full`: H_M = H_adm < 1/2
- `bivariate_recovery`: Corollary 5.2 — N=2 specialization

## Perron Decomposition (`PerronDecomposition.lean`)
- `perronCoeff`: ϖ = u^T x
- `perronRemainder`: r = x - ϖv
- `perron_decomp`: **Proposition 6.5** — x = ϖv + r
- `perron_remainder_orthogonal`: u^T r = 0
- `perron_decomp_unique_coeff`: uniqueness of ϖ
- `perron_decomp_unique_remainder`: uniqueness of r
- `error_recursion_bound`: **Proposition 6.3** — finite-horizon error bound

## Synchronization (`Synchronization.lean`)
- `subcritical_convergence`: **Theorem 6.1(i)** — ρ^m → 0 when ρ < 1
- `supercritical_divergence`: **Theorem 6.1(ii)** — ρ^m → ∞ when ρ > 1
- `spectral_gap_decay`: **Theorem 6.6** — (ρ₂/ρ(A))^m → 0
- `off_perron_relative_decay`: off-Perron decay identity
- `phase_dichotomy`: ρ(A) ≤ 1 ∨ 1 < ρ(A)

## Compression and Hedging (`Compression.lean`)
- `variance_lower_bound`: conditional variance decomposition
- `compression_gap`: **Theorem 8.6(i)** — compression gap lower bound
- `hedge_shortfall`: **Theorem 8.6(ii)** — hedge shortfall lower bound
- `strongly_convex_jensen_gap_nonneg`: Jensen gap nonnegativity
- `affine_hedge_shortfall`: **Corollary 8.7** — affine claims
- `latent_convexity_gap`: **Proposition 8.9** — convexity gap
- `latent_convexity_gap_strict`: strictness under nondegeneracy
- `loading_transfer_bounds`: **Proposition 8.8** — loading bounds
- `loading_nonzero`: loading positivity
- `visible_summary_bound`: **Corollaries 8.10–8.15** — visible summary bounds
- `srisk_compressed`: **Corollary 8.14** — SRISK compression

## Phase Structure (`PhaseStructure.lean`)
- `smooth_degenerate_phase`: **Theorem 7.8(i)** — smooth ⟹ E_adm = ∅
- `rough_observable_phase`: **Theorem 7.8(ii)** — roughness under admissibility
- `phase_classification`: **Theorem 7.8** — phase dichotomy
- `smooth_phase_no_admissible`: no admissible edges in smooth phase

## Riemann–Liouville Scaling (`RLScaling.lean`)
- `RL_kappa`: Definition of the scaling constant κ(H)
- `RL_kappa_term_pos`: positivity of 1/(2H)
- `RL_integral_substitution`: h^{2H} > 0
- `RL_fresh_piece`: h^{2H}/(2H) > 0
-/
