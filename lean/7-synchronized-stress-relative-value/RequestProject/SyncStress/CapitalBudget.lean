/-
# Proposition 7.1: Capital-budget admissibility

The drawdown breach amount is `max{MDD - B, 0}`.

From: "Synchronized Stress Relative Value" by J. Vidal Llauradó (2026).
-/
import Mathlib

noncomputable section

/-! ## Proposition 7.1 (Capital-budget admissibility)

If the drawdown budget B is breached (MDD > B), the breach amount is MDD - B.
Otherwise it is 0. The breach amount is always max{MDD - B, 0}. -/

/-
**Proposition 7.1.** The drawdown breach amount equals `max{MDD - B, 0}`.
    This captures: the budget is breached iff `MDD > B`, and the breach size is
    the excess `MDD - B` when positive, zero otherwise.
-/
theorem capital_budget_breach (MDD B : ℝ) :
    (if MDD > B then MDD - B else 0) = max (MDD - B) 0 := by
  grind

/-
The drawdown budget is not breached iff `MDD ≤ B`.
-/
theorem capital_budget_admissible_iff (MDD B : ℝ) :
    MDD ≤ B ↔ max (MDD - B) 0 = 0 := by
  grind

end