/-
# Theorem 6.5: No-look-ahead lower-bound sizing

Composition of measurable functions is measurable. The executable book is
measurable w.r.t. the formation-date σ-algebra.

From: "Synchronized Stress Relative Value" by J. Vidal Llauradó (2026).
-/
import Mathlib

noncomputable section

open MeasureTheory

/-! ## Theorem 6.5 (No-look-ahead lower-bound sizing)

The sizing map `(LB, R, caps) ↦ min{(LB)₊/(λR), x̄_margin, x̄_tail, x̄_cost}`
is Borel measurable. Composition with measurable inputs gives a measurable size.

We formalize the key mathematical content: the sizing function is measurable,
and composition with measurable inputs yields a measurable result. -/

/-- The sizing function: `(LB, R, caps) ↦ min{(LB)₊/(λR), x̄_margin, x̄_tail, x̄_cost}` -/
def sizingFun (lam : ℝ) (LB R x_margin x_tail x_cost : ℝ) : ℝ :=
  min (min (max LB 0 / (lam * R)) x_margin) (min x_tail x_cost)

/-
**Theorem 6.5.** The sizing function is Borel measurable (as a function of its inputs).
-/
theorem sizing_measurable (lam : ℝ) :
    Measurable (fun p : ℝ × ℝ × ℝ × ℝ × ℝ =>
      sizingFun lam p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) := by
  apply_rules [ Measurable.min, Measurable.max, Measurable.mul, measurable_const, measurable_fst, measurable_snd.fst, measurable_snd.snd.fst, measurable_snd.snd.snd.fst, measurable_snd.snd.snd.snd ];
  exact Measurable.inv ( measurable_const.mul measurable_snd.fst )

/-
**Theorem 6.5 (Composition).** When all inputs are measurable w.r.t. a
    σ-algebra, the sizing output is measurable w.r.t. that σ-algebra.
-/
theorem no_lookahead_sizing {Ω : Type*} [MeasurableSpace Ω]
    (lam : ℝ)
    (LB R x_margin x_tail x_cost : Ω → ℝ)
    (hLB : Measurable LB) (hR : Measurable R)
    (hm : Measurable x_margin) (ht : Measurable x_tail) (hc : Measurable x_cost) :
    Measurable (fun ω => sizingFun lam (LB ω) (R ω) (x_margin ω) (x_tail ω) (x_cost ω)) := by
  unfold sizingFun; apply_rules [ Measurable.min, Measurable.max, Measurable.div, Measurable.mul, hLB, hR, hm, ht, hc ] ;
  · exact measurable_const;
  · exact measurable_const

end