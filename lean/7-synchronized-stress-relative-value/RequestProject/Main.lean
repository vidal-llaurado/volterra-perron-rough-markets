/-
# Synchronized Stress Relative Value — Formalization

Lean 4 formalization of the mathematical results from:
"Synchronized Stress Relative Value: Public-Neutral Option Books under
 Latent Stress Compression" by J. Vidal Llauradó (2026).

## Contents

- `Defs`: Core definitions (public neutrality, sync edge, sellability, carrier weights)
- `CarrierExistence`: Proposition 5.4 — existence and uniqueness of carrier weights
- `StressConvexity`: Proposition 5.5 — OLS characterization of the hedge ratio
- `FiniteBookOpt`: Theorem 5.6 — finite public-neutral book optimization
- `LowerBound`: Propositions 6.2 & 6.4 — lower-bound certificate and sizing
- `Measurability`: Theorem 6.5 — no-look-ahead lower-bound sizing
- `CapitalBudget`: Proposition 7.1 — capital-budget admissibility
-/
import RequestProject.SyncStress.Defs
import RequestProject.SyncStress.CarrierExistence
import RequestProject.SyncStress.StressConvexity
import RequestProject.SyncStress.FiniteBookOpt
import RequestProject.SyncStress.LowerBound
import RequestProject.SyncStress.Measurability
import RequestProject.SyncStress.CapitalBudget
