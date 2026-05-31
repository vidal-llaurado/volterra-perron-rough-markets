/-
# Perron Stress Pricing: Core Definitions

Formalization of the core definitions from:
  "Perron Stress Pricing under Public Compression"
  by J. Vidal Llauradó (2026)

This file sets up the measure-theoretic framework and defines the key objects:
latent loading, public shadow, visible hedge, public-equivalent densities,
and residual pricing.
-/
import Mathlib

open MeasureTheory MeasurableSpace Filter
open scoped ENNReal NNReal BigOperators

noncomputable section

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} {μ : Measure Ω}

namespace PerronStress

/-! ## Section 2: Setup -/

/-- The setup for Perron stress pricing:
  - `mH` is the public option information field
  - `mG` is the larger public terminal market information field
  - `mK` is the latent Perron stress information field
  - `m₀` is the full terminal information field
  with `mH ≤ mG ≤ mK ≤ m₀`. -/
structure Setup (Ω : Type*) (m₀ : MeasurableSpace Ω) (μ : Measure Ω) where
  mH : MeasurableSpace Ω
  mG : MeasurableSpace Ω
  mK : MeasurableSpace Ω
  hHG : mH ≤ mG
  hGK : mG ≤ mK
  hK0 : mK ≤ m₀
  hSigmaFiniteH : SigmaFinite (μ.trim (le_trans (le_trans hHG hGK) hK0))
  hSigmaFiniteG : SigmaFinite (μ.trim (le_trans hGK hK0))
  hSigmaFiniteK : SigmaFinite (μ.trim hK0)

variable [IsFiniteMeasure μ]

/-- Definition 2.1: Latent loading `L_X^Q = E_Q[X | K]`. -/
def latentLoading (S : Setup Ω m₀ μ) (X : Ω → ℝ) : Ω → ℝ :=
  μ[X | S.mK]

/-- Definition 2.1: Public calibration shadow `X_H^Q = E_Q[L_X^Q | H]`. -/
def publicShadow (S : Setup Ω m₀ μ) (X : Ω → ℝ) : Ω → ℝ :=
  μ[latentLoading S X | S.mH]

/-- Definition 2.4: The class of public-equivalent densities relative to H.
    Z ∈ Z_H iff Z > 0, E[Z] = 1, and E[Z | H] = 1 a.e. -/
def IsPublicEquivDensity (S : Setup Ω m₀ μ) (Z : Ω → ℝ) : Prop :=
  (∀ᵐ ω ∂μ, 0 < Z ω) ∧
  ∫ ω, Z ω ∂μ = 1 ∧
  μ[Z | S.mH] =ᵐ[μ] fun _ => (1 : ℝ)

/-- Definition 2.4: The dynamic-safe density class relative to G.
    Z ∈ Z_G iff Z > 0, E[Z] = 1, and E[Z | G] = 1 a.e. -/
def IsDynamicSafeDensity (S : Setup Ω m₀ μ) (Z : Ω → ℝ) : Prop :=
  (∀ᵐ ω ∂μ, 0 < Z ω) ∧
  ∫ ω, Z ω ∂μ = 1 ∧
  μ[Z | S.mG] =ᵐ[μ] fun _ => (1 : ℝ)

/-- Definition 2.8: Public residual directions `R_H^2`:
    `{R ∈ L²(Q) : E_Q[R | H] = 0}` -/
def IsPublicResidual (S : Setup Ω m₀ μ) (R : Ω → ℝ) : Prop :=
  μ[R | S.mH] =ᵐ[μ] 0

/-- Bounded local residual tilt: Z_η = 1 + η R -/
def localTilt (η : ℝ) (R : Ω → ℝ) : Ω → ℝ :=
  fun ω => 1 + η * R ω

/-- Definition 4.1: Compression-consistent price interval endpoints.
    Π⁻(X) = E[X] - η̄ |E[XR]|, Π⁺(X) = E[X] + η̄ |E[XR]| -/
def priceIntervalLower (μ : Measure Ω) (X R : Ω → ℝ) (η_bar : ℝ) : ℝ :=
  ∫ ω, X ω ∂μ - η_bar * |∫ ω, X ω * R ω ∂μ|

def priceIntervalUpper (μ : Measure Ω) (X R : Ω → ℝ) (η_bar : ℝ) : ℝ :=
  ∫ ω, X ω ∂μ + η_bar * |∫ ω, X ω * R ω ∂μ|

/-- Definition 5.1: The public shadow, baseline price and residual price.
    Π₀(X) = E_Q[X] (the baseline scalar price). -/
def baselinePrice (μ : Measure Ω) (X : Ω → ℝ) : ℝ :=
  ∫ ω, X ω ∂μ

/-- Definition 5.1: The residual price contribution under tilt parameter η.
    Π_R^res(X; η) = η · ⟨L_X^Q - E[L_X^Q | H], R⟩_{L²(Q)} -/
def residualPrice (S : Setup Ω m₀ μ) (X R : Ω → ℝ) (η : ℝ) : ℝ :=
  η * ∫ ω, (latentLoading S X ω - publicShadow S X ω) * R ω ∂μ

end PerronStress

end

