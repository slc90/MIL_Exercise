import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Group.Abs

set_option linter.style.cdot false

section
variable (a b c d : ℝ)

example : max a b = max b a := by
  apply le_antisymm
  repeat
  apply max_le
  . apply le_max_right
  . apply le_max_left

example : min (min a b) c = min a (min b c) := by
  apply le_antisymm
  . have h1 : min (min a b) c <= a := by
      calc min (min a b) c
        _ <= min a b := by apply min_le_left
        _ <= a := by apply min_le_left
    have h2 : min (min a b) c <= b := by
      calc min (min a b) c
        _ <= (min a b) := by apply min_le_left
        _ <= b := by apply min_le_right
    have h3 : min (min a b) c <= c := by
      calc min (min a b) c
        _ <= c := by apply min_le_right
    have h4 : min (min a b) c <= min b c := by
      apply le_min h2 h3
    apply le_min h1 h4
  . have h1 : min a (min b c) <= a := by apply min_le_left
    have h2 : min a (min b c) <= b := by
      calc min a (min b c)
        _ <= min b c := by apply min_le_right
        _ <= b := by apply min_le_left
    have h3 : min a (min b c) <= min a b := by
      apply le_min h1 h2
    have h4 : min a (min b c) <= c := by
      calc min a (min b c)
        _ <= min b c := by apply min_le_right
        _ <= c := by apply min_le_right
    apply le_min h3 h4

theorem aux : min a b + c ≤ min (a + c) (b + c) := by
  have h1 : min a b + c <= a + c := by
    apply add_le_add_right
    apply min_le_left
  have h2 : min a b + c <= b + c := by
    apply add_le_add_right
    apply min_le_right
  apply le_min h1 h2

example : min a b + c = min (a + c) (b + c) := by
  apply le_antisymm
  . apply aux
  . have h : min (a + c) (b + c) = min (a + c) (b + c) - c + c := by rw [sub_add_cancel]
    rw [h]
    apply add_le_add_right
    rw [sub_eq_add_neg]
    apply le_trans
    . apply aux
    . rw [add_neg_cancel_right, add_neg_cancel_right]

example : |a| - |b| ≤ |a - b| := by
  have h : |a - b| + |b| - |b| = |a - b| := by
    apply add_sub_cancel_right
  rw [← h]
  apply add_le_add_right
  -- why abs_add doesn't exist?
  -- apply abs_add
  sorry
end


section
open Nat
variable (w x y z : ℕ)

example (h : x ∣ w) : x ∣ y * (x * z) + x ^ 2 + w ^ 2 := by
  apply dvd_add
  . apply dvd_add
    . apply dvd_mul_of_dvd_right
      apply dvd_mul_right
    . apply dvd_mul_left
  . apply dvd_mul_of_dvd_right h

end

section
variable (m n : ℕ)

end
