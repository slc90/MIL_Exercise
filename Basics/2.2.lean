import Mathlib.Tactic.NormNum

namespace MyRing
variable {R : Type*} [Ring R]
variable {G : Type*} [Group G]

theorem add_zero (a : R) : a + 0 = a := by rw [add_comm, zero_add]

theorem add_neg_cancel (a : R) : a + -a = 0 := by rw [add_comm, neg_add_cancel]

theorem neg_add_cancel_left (a b : R) : -a + (a + b) = b := by
  rw [← add_assoc, neg_add_cancel, zero_add]

theorem add_neg_cancel_right (a b : R) : a + b + -b = a := by
  rw [add_assoc]
  rw [add_neg_cancel]
  rw [add_zero]

theorem add_left_cancel {a b c : R} (h : a + b = a + c) : b = c := by
  rw [← neg_add_cancel_left a b]
  rw [h]
  rw [neg_add_cancel_left]

theorem add_right_cancel {a b c : R} (h : a + b = c + b) : a = c := by
  rw [← add_neg_cancel_right a b]
  rw [h]
  rw [add_neg_cancel_right]

theorem zero_mul (a : R) : 0 * a = 0 := by
  have h : 0 * a + 0 * a = 0 + 0 * a := by
    rw [← add_mul]
    rw [add_zero]
    rw [add_comm]
    rw [add_zero]
  rw [add_right_cancel h]

theorem neg_eq_of_add_eq_zero {a b : R} (h : a + b = 0) : -a = b := by
  rw [← neg_add_cancel_left a b]
  rw [h]
  rw [add_zero]

theorem eq_neg_of_add_eq_zero {a b : R} (h : a + b = 0) : a = -b := by
  rw [← add_neg_cancel_right a b]
  rw [h]
  rw [add_comm]
  rw [add_zero]

theorem neg_zero : (-0 : R) = 0 := by
  apply neg_eq_of_add_eq_zero
  rw [add_zero]

theorem neg_neg (a : R) : - -a = a := by
  have h : -a + a = 0 := by
    nth_rw 2 [← add_zero a]
    apply neg_add_cancel_left
  apply neg_eq_of_add_eq_zero
  exact h

theorem self_sub (a : R) : a - a = 0 := by
  rw [sub_eq_add_neg]
  rw [add_comm]
  nth_rw 2 [← add_zero a]
  apply neg_add_cancel_left

theorem one_add_one_eq_two : 1 + 1 = (2 : R) := by
  norm_num

theorem two_mul (a : R) : 2 * a = a + a := by
  rw [← one_add_one_eq_two]
  rw [add_mul]
  rw [one_mul]

theorem mul_inv_cancel (a : G) : a * a⁻¹ = 1 := by
  have h : (a * a⁻¹)⁻¹ * (a * a⁻¹ * (a * a⁻¹)) = 1 := by
    rw [mul_assoc, ← mul_assoc a⁻¹ a, inv_mul_cancel, one_mul, inv_mul_cancel]
  rw [← h]
  rw [← mul_assoc]
  rw [inv_mul_cancel]
  rw [one_mul]

theorem mul_one (a : G) : a * 1 = a := by
  rw [← inv_mul_cancel a]
  rw [← mul_assoc]
  rw [mul_inv_cancel]
  rw [one_mul]

theorem mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  rw [← one_mul (a *b)⁻¹]
  rw [← inv_mul_cancel b]
  nth_rw 2 [← one_mul b]
  rw [← inv_mul_cancel a]
  rw [mul_assoc]
  rw [mul_assoc a⁻¹]
  rw [mul_assoc a⁻¹]
  rw [mul_inv_cancel]
  rw [mul_one]

end MyRing
