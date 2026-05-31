/-
# Perron Stress Pricing under Public Compression

Lean 4 / Mathlib formalization of key results from:
  "Perron Stress Pricing under Public Compression:
   Residual Price Intervals, Synchronized Stress, and Visible Hedging"
  by J. Vidal Llauradó (2026)

## Overview

The paper studies pricing, hedging, and capital for latent Perron stress claims
under incomplete public option-surface information. The mathematical framework
uses orthogonal projections in L²(Q) (conditional expectations) on a probability
space with nested sub-sigma-fields H ⊆ G ⊆ K ⊆ F.

## Formalized results

### Definitions (PerronStress.Defs)
- Setup structure with nested sigma-fields
- Latent loading, public shadow
- Public-equivalent and dynamic-safe densities
- Public residual directions
- Local tilt, price intervals, baseline and residual pricing

### Public Equivalence (PerronStress.PublicEquivalence)
- Proposition 2.4: E[ZY] = E[Y] for all bounded H-measurable Y ⟺ E[Z|H] = 1
- Tower property: dynamic-safe ⟹ public-equivalent
- Lemma 3.2: Public prices are preserved

### Residual Tilts (PerronStress.ResidualTilts)
- Theorem 3.3: Bounded local residual tilts (Z_η = 1 + ηR is public-equivalent)
- Theorem 4.2: Explicit residual price interval
- Theorem 4.5: Perron stress pricing decomposition

### Nested Residuals (PerronStress.NestedResiduals)
- Theorem 2.7: Pythagorean identity for nested conditional expectations
- Theorem 5.1: Visible hedge orthogonality
- Theorem 5.3: Three-part visible hedge decomposition
-/

import RequestProject.PerronStress.Defs
import RequestProject.PerronStress.PublicEquivalence
import RequestProject.PerronStress.ResidualTilts
import RequestProject.PerronStress.NestedResiduals
