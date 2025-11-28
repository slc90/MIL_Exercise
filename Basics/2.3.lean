import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option linter.style.cdot false

variable (a b c d e : ℝ)
open Real

example (h₀ : a ≤ b) (h₁ : b < c) (h₂ : c ≤ d) (h₃ : d < e) : a < e := by
  have hac : a < c := by
    apply lt_of_le_of_lt h₀ h₁
  have hce : c < e := by
    apply lt_of_le_of_lt h₂ h₃
  apply lt_trans hac hce

example (h₀ : d ≤ e) : c + exp (a + d) ≤ c + exp (a + e) := by
  apply add_le_add_left
  apply exp_le_exp.mpr
  apply add_le_add_left
  exact h₀

example (h : a ≤ b) : log (1 + exp a) ≤ log (1 + exp b) := by
  have h₀ : 0 < 1 + exp a := by
    apply add_pos
    . norm_num
    . apply exp_pos
  apply log_le_log h₀
  apply add_le_add_left
  apply exp_le_exp.mpr
  exact h

example (h : a ≤ b) : c - exp b ≤ c - exp a := by
  apply add_le_add_left
  apply neg_le_neg_iff.mpr
  apply exp_le_exp.mpr
  exact h

example : |a*b| ≤ (a^2 + b^2)/2 := by
  apply abs_le'.mpr
  constructor
  . have h : 0 <= (a ^ 2 + b ^ 2) / 2 - a * b :=
      calc (a ^ 2 + b ^ 2) / 2 - a * b
        _ = (a - b) ^ 2 / 2 := by ring
        _ >= 0 := by
          apply div_nonneg
          . apply pow_two_nonneg
          . norm_num
    linarith
  . have h : 0 <= (a ^ 2 + b ^ 2) / 2 + a * b :=
      calc (a ^ 2 + b ^ 2) / 2 + a * b
        _ = (a + b) ^ 2 / 2 := by ring
        _ >= 0 := by
          apply div_nonneg
          . apply pow_two_nonneg
          . norm_num
    linarith
