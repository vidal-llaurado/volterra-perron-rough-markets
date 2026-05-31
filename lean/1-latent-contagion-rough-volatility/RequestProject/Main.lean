/-
# Latent Volatility Contagion in Rough Volatility Models
## Spectral Thresholds and Detectability

Formalization of key results from:
  J. Vidal Llauradó, "Latent Volatility Contagion in Rough Volatility Models:
  Spectral Thresholds and Detectability" (2026).

This file formalizes the core threshold structure of the paper:
- The p-series summability criterion underlying the Hilbert–Schmidt condition
- The Feldman–Hájek spectral threshold (δ > 1/4)
- The pricing visibility threshold (H_XY = H_Y)
- The latent contagion regime and its nonemptiness
- The cumulative spectral energy growth classification
-/

import Mathlib

open scoped BigOperators
open Real Filter Asymptotics Topology

set_option maxHeartbeats 8000000

noncomputable section

/-! ## Hurst Parameter Range

The paper works with Hurst exponents H_Y, H_XY ∈ (0, 1/2).
We define the valid range and the smoothing gap δ = H_XY - H_Y.
-/

/-- Valid Hurst parameter range for rough volatility: H ∈ (0, 1/2). -/
def IsHurstParam (H : ℝ) : Prop := 0 < H ∧ H < 1 / 2

/-- The smoothing gap δ = H_XY - H_Y. -/
def smoothingGap (H_Y H_XY : ℝ) : ℝ := H_XY - H_Y

/-! ## Part 1: p-Series Summability (Foundation for Theorem 5.9)

The Hilbert–Schmidt condition for the relative covariance operator reduces to
summability of the p-series ∑ n^{-4δ}. This is the analytic core of the
Feldman–Hájek threshold.
-/

/-- **p-series summability criterion** (Theorem 5.9(iii) core).
The series `∑ n^{-α}` converges if and only if `α > 1`.
This is the Mathlib result `Real.summable_one_div_nat_rpow` restated. -/
theorem pSeries_summable_iff (α : ℝ) :
    (Summable fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ α) ↔ 1 < α :=
  Real.summable_one_div_nat_rpow

/-
The eigenvalue series `∑ n^{-4δ}` converges iff `δ > 1/4`.
This is the direct analytic statement behind Theorem 5.9(iii):
  `R̂_{Y,XY} ∈ 𝔖₂ ⟺ δ > 1/4`.
-/
theorem hilbertSchmidt_summability_iff (δ : ℝ) :
    (Summable fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ (4 * δ)) ↔ 1 / 4 < δ := by
  exact ⟨ fun h => by contrapose! h; exact Real.summable_one_div_nat_rpow.not.mpr ( by linarith ), fun h => Real.summable_one_div_nat_rpow.mpr ( by linarith ) ⟩

/-! ## Part 2: Feldman–Hájek Threshold (Theorem 5.10)

The Feldman–Hájek dichotomy for centred Gaussian measures reduces equivalence vs.
mutual singularity to a Hilbert–Schmidt condition on the relative covariance operator.
We formalize this as an abstract threshold result parameterized by the spectral gap.
-/

/-- Classification of Gaussian measure comparison in the smoothing regime.
Corresponds to Theorem 5.10 (Equivalence threshold in the smoothing regime). -/
inductive GaussianComparison where
  | equivalent   : GaussianComparison
  | singular     : GaussianComparison

/-- **Feldman–Hájek threshold** (Theorem 5.10).
In the smoothing regime (δ > 0), the coupled and uncoupled Gaussian measures are:
- equivalent if δ > 1/4,
- mutually singular if 0 < δ ≤ 1/4. -/
def feldmanHajekThreshold (δ : ℝ) (_hδ : 0 < δ) : GaussianComparison :=
  if 1 / 4 < δ then GaussianComparison.equivalent
  else GaussianComparison.singular

/-
In the equivalence regime, δ > 1/4.
-/
theorem feldmanHajek_equiv_iff_gt (δ : ℝ) (hδ : 0 < δ) :
    feldmanHajekThreshold δ hδ = GaussianComparison.equivalent ↔ 1 / 4 < δ := by
  unfold feldmanHajekThreshold; aesop

/-
In the singular regime, 0 < δ ≤ 1/4.
-/
theorem feldmanHajek_singular_iff_le (δ : ℝ) (hδ : 0 < δ) :
    feldmanHajekThreshold δ hδ = GaussianComparison.singular ↔ δ ≤ 1 / 4 := by
  unfold feldmanHajekThreshold; split_ifs <;> aesop

/-! ## Part 3: Pricing Threshold (Theorem 7.7)

The ATM Bachelier skew satisfies:
  ψ(T) = C̃_Y · T^{H_Y - 1/2} + C̃_{XY} · T^{H_{XY} - 1/2} + o(T^{H_* - 1/2})

The leading-order term is determined by the smaller Hurst exponent since T → 0⁺
and both exponents H - 1/2 are negative.
-/

/-
When `a < b < 0`, we have `T^a` dominates `T^b` as `T → 0⁺`.
This is the key asymptotic comparison underlying the pricing threshold.
-/
theorem power_dominance_at_zero {a b : ℝ} (hab : a < b) (_hb : b < 0) :
    (fun T : ℝ => T ^ b) =o[nhdsWithin 0 (Set.Ioi 0)] (fun T : ℝ => T ^ a) := by
  -- We need to show T^b = o(T^a) as T → 0⁺. Equivalently T^(b-a) → 0, since b - a > 0 and T → 0⁺.
  have h_lim : Filter.Tendsto (fun T : ℝ => T^(b-a)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    convert Filter.Tendsto.rpow ( Filter.tendsto_id.mono_left inf_le_left ) tendsto_const_nhds _ using 1 <;> norm_num [ hab.ne', _hb.ne' ];
    · rw [ Real.zero_rpow ( by linarith ) ];
    · bv_omega;
  rw [ Asymptotics.isLittleO_iff_tendsto' ];
  · refine' h_lim.congr' ( by filter_upwards [ self_mem_nhdsWithin ] with x hx using by rw [ ← Real.rpow_sub hx ] );
  · filter_upwards [ self_mem_nhdsWithin ] with x hx hx' using absurd hx' <| ne_of_gt <| Real.rpow_pos_of_pos hx _

/-
**Pricing threshold** (Theorem 7.7, simplified).
When H_XY > H_Y (smoothing regime), the cross-asset skew component T^{H_XY - 1/2}
is asymptotically negligible compared to the idiosyncratic component T^{H_Y - 1/2}
as T → 0⁺, because H_XY - 1/2 > H_Y - 1/2 and both are negative.
-/
theorem pricing_threshold_smoothing
    (H_Y H_XY : ℝ) (_hY : IsHurstParam H_Y) (hXY : IsHurstParam H_XY)
    (hsmooth : H_Y < H_XY) :
    (fun T : ℝ => T ^ (H_XY - 1/2)) =o[nhdsWithin 0 (Set.Ioi 0)]
      (fun T : ℝ => T ^ (H_Y - 1/2)) := by
  have := @power_dominance_at_zero ( H_Y - 1 / 2 ) ( H_XY - 1 / 2 ) ?_ ?_ <;> norm_num at *;
  · convert this using 1;
  · grind;
  · exact hXY.2

/-! ## Part 4: Latent Contagion Regime (Proposition 8.1)

The latent contagion regime is the interval H_Y < H_XY ≤ H_Y + 1/4, where:
- The cross-asset component is NOT visible at leading order in the pricing skew
  (because H_XY > H_Y)
- The coupled and uncoupled Gaussian path laws are mutually SINGULAR
  (because δ = H_XY - H_Y ≤ 1/4)
-/

/-- The latent contagion regime: price-invisible but path-detectable. -/
def IsLatentContagionRegime (H_Y H_XY : ℝ) : Prop :=
  H_Y < H_XY ∧ H_XY ≤ H_Y + 1 / 4

/-
In the latent contagion regime, the smoothing gap satisfies 0 < δ ≤ 1/4.
-/
theorem latent_regime_gap (H_Y H_XY : ℝ) (h : IsLatentContagionRegime H_Y H_XY) :
    0 < smoothingGap H_Y H_XY ∧ smoothingGap H_Y H_XY ≤ 1 / 4 := by
  exact ⟨ sub_pos.mpr h.1, sub_le_iff_le_add'.mpr h.2 ⟩

/-
In the latent regime, the Feldman–Hájek comparison gives mutual singularity.
-/
theorem latent_regime_singular (H_Y H_XY : ℝ) (h : IsLatentContagionRegime H_Y H_XY) :
    feldmanHajekThreshold (smoothingGap H_Y H_XY) (by unfold smoothingGap; linarith [h.1]) =
      GaussianComparison.singular := by
  unfold IsLatentContagionRegime at *;
  exact if_neg ( by linarith [ h.1, h.2, show smoothingGap H_Y H_XY ≤ 1 / 4 by unfold smoothingGap; linarith ] )

/-
**Nonemptiness of the latent contagion regime** (Proposition 8.1, Remark).
For every valid Hurst parameter H_Y ∈ (0, 1/2), there exists H_XY ∈ (0, 1/2)
in the latent contagion regime.
-/
theorem latent_regime_nonempty (H_Y : ℝ) (hY : IsHurstParam H_Y) :
    ∃ H_XY : ℝ, IsHurstParam H_XY ∧ IsLatentContagionRegime H_Y H_XY := by
  -- Set H_XY to be H_Y + min(1/8, (1/2 - H_Y)/2)
  use H_Y + min (1 / 8) ((1 / 2 - H_Y) / 2);
  constructor <;> constructor <;> cases min_cases ( 1 / 8 ) ( ( 1 / 2 - H_Y ) / 2 ) <;> linarith [ hY.1, hY.2 ]

/-! ## Part 5: Spectral Asymptotics Classification (Corollary 5.11)

The cumulative latent spectral energy E_latent(N) = ∑_{n=1}^{N} λ_n(R_{Y,XY})
has different growth rates depending on δ:
- If 0 < δ < 1/2: E_latent(N) grows as N^{1-2δ} (polynomial)
- If δ = 1/2: E_latent(N) grows as log N
- If δ > 1/2: E_latent(N) is bounded

In the latent regime (0 < δ ≤ 1/4), the growth is polynomial with exponent
1 - 2δ ≥ 1/2, confirming divergence.
-/

/-
In the latent regime, the spectral energy exponent 1 - 2δ is at least 1/2,
ensuring polynomial divergence (Corollary 5.11).
-/
theorem latent_energy_exponent_lower_bound
    (H_Y H_XY : ℝ) (h : IsLatentContagionRegime H_Y H_XY) :
    1 / 2 ≤ 1 - 2 * smoothingGap H_Y H_XY := by
  unfold IsLatentContagionRegime smoothingGap at * ; linarith

/-
The spectral energy exponent is strictly positive in the latent regime,
confirming the divergence of cumulative spectral mass.
-/
theorem latent_energy_exponent_positive
    (H_Y H_XY : ℝ) (h : IsLatentContagionRegime H_Y H_XY) :
    0 < 1 - 2 * smoothingGap H_Y H_XY := by
  linarith [ h.1, h.2, latent_energy_exponent_lower_bound H_Y H_XY h ]

/-! ## Part 6: Threshold Summary (Proposition 8.1)

The complete classification of the three regimes.
-/

/-- Classification of the contagion regime. -/
inductive ContagionRegime where
  | pricingVisible  : ContagionRegime  -- H_XY ≤ H_Y
  | latent          : ContagionRegime  -- H_Y < H_XY ≤ H_Y + 1/4
  | equivalent      : ContagionRegime  -- H_XY > H_Y + 1/4

/-- **Threshold classification** (Proposition 8.1).
Classifies the contagion regime based on the Hurst exponents. -/
def classifyRegime (H_Y H_XY : ℝ) : ContagionRegime :=
  if H_XY ≤ H_Y then ContagionRegime.pricingVisible
  else if H_XY ≤ H_Y + 1 / 4 then ContagionRegime.latent
  else ContagionRegime.equivalent

/-
The pricing-visible regime corresponds to H_XY ≤ H_Y.
-/
theorem classify_pricingVisible_iff (H_Y H_XY : ℝ) :
    classifyRegime H_Y H_XY = ContagionRegime.pricingVisible ↔ H_XY ≤ H_Y := by
  constructor <;> intro h <;> unfold classifyRegime at * <;> aesop

/-
The latent regime corresponds to H_Y < H_XY ≤ H_Y + 1/4.
-/
theorem classify_latent_iff (H_Y H_XY : ℝ) :
    classifyRegime H_Y H_XY = ContagionRegime.latent ↔
      H_Y < H_XY ∧ H_XY ≤ H_Y + 1 / 4 := by
  unfold classifyRegime;
  grind

/-
The equivalent regime corresponds to H_XY > H_Y + 1/4.
-/
theorem classify_equivalent_iff (H_Y H_XY : ℝ) :
    classifyRegime H_Y H_XY = ContagionRegime.equivalent ↔
      H_Y + 1 / 4 < H_XY := by
  unfold classifyRegime;
  split_ifs <;> norm_num;
  · linarith;
  · linarith;
  · linarith

/-
The quarter-gap 1/4 is sharp: it is the unique threshold separating
the singular and equivalent regimes.
-/
theorem quarter_gap_sharp :
    ∀ δ : ℝ, 0 < δ →
      ((Summable fun n : ℕ => ((1 : ℝ) / (n : ℝ) ^ (4 * δ))) ↔ 1 / 4 < δ) := by
  exact fun δ _ => hilbertSchmidt_summability_iff δ

/-! ## Part 7: The 1/4 Gap Origin (Remark 8.4)

The 1/4 gap arises from the Schatten-4 membership of the fractional integral
operator I_{0+}^δ: since s_n(I_{0+}^δ) ~ n^{-δ}, the Hilbert-Schmidt condition
for R = BB* becomes ∑ n^{-4δ} < ∞, which holds iff δ > 1/4.
-/

/-
The Schatten-p membership threshold for the spectral sequence n^{-δ}:
∑ n^{-pδ} < ∞ iff pδ > 1, i.e., δ > 1/p.
-/
theorem schatten_p_threshold (p : ℝ) (hp : 0 < p) (δ : ℝ) (_hδ : 0 < δ) :
    (Summable fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ (p * δ)) ↔ 1 / p < δ := by
  -- Apply the theorem pseries_summable_iff with α = p*δ.
  have h_summable : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ (p * δ)) ↔ 1 < p * δ := by
    exact pSeries_summable_iff (p * δ)
  rw [ h_summable, div_lt_iff₀' hp ]

end