/-
  # Volterra–Perron Pricing of the Option Manifold

  Lean formalization of selected theorems from:

    J. Vidal Llauradó, "Volterra–Perron Pricing of the Option Manifold" (2026).

  ## Structure

  The formalization is organized into the following modules:

  - `PerronProjector`: Perron spectral projector, gauge invariance (Def 3.9, Prop 3.10)
  - `PublicQuotient`: Public-observable quotient, non-identification (Thm 5.2, Thm 5.5)
  - `CompressionFactorization`: Tower property / compression factorization (Prop 3.8, Lem 5.9–5.10)
  - `CalendarConvexOrder`: Calendar convex-order restriction (Thm 3.5)
  - `BachelierPricing`: Bachelier formula, put-call parity, Greeks (Sec 10)
  - `PhaseStratification`: Phase stratification, hedge formula (Thm 6.3, Thm 10.6)
  - `Identifiability`: Power-exponential route identifiability (Thm 4.3, Cor 4.4)
-/

import RequestProject.PerronProjector
import RequestProject.PublicQuotient
import RequestProject.CompressionFactorization
import RequestProject.CalendarConvexOrder
import RequestProject.BachelierPricing
import RequestProject.PhaseStratification
import RequestProject.Identifiability
