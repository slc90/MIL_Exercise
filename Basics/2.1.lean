import Mathlib.Data.Real.Basic

variable (a b c d e f : ℝ)

example (a b c : ℝ) : c * b * a = b * (a * c) := by
  rw [mul_comm c b]
  rw [mul_assoc b c a]
  rw [mul_comm a c]

example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  rw [← mul_assoc a b c]
  rw [mul_comm a b]
  rw [mul_assoc b a c]

example (a b c : ℝ) : a * (b * c) = b * (c * a) := by
  rw [mul_comm]
  rw [mul_assoc]

example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  rw [mul_comm a]
  rw [mul_assoc b]
  rw [mul_comm c]

example (a b c d e f : ℝ) (h : b * c = e * f) : a * b * c * d = a * e * f * d := by
  rw [mul_assoc a]
  rw [h]
  rw [← mul_assoc]

example (a b c d : ℝ) (hyp : c = b * a - d) (hyp' : d = a * b) : c = 0 := by
  rw [hyp]
  rw [hyp']
  rw [mul_comm b]
  rw [sub_self]

example : (a + b) * (c + d) = a * c + a * d + b * c + b * d := by
  calc (a + b) * (c + d)
    _ = a * (c + d) + b * (c + d) := by rw [add_mul]
    _ = a * c + a * d + b * (c + d) := by rw [mul_add]
    _ = a * c + a * d + (b * c + b * d) := by rw [mul_add]
    _ = a * c + a * d + b * c + b * d := by rw [← add_assoc]

example (a b : ℝ) : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
  calc (a + b) * (a - b)
    _ = a * (a - b) + b * (a - b) := by rw [add_mul]
    _ = a * a - a * b + b * (a - b) := by rw [mul_sub]
    _ = a * a - a * b + (b * a - b * b) := by rw [mul_sub]
    _ = a * a - a * b + b * a - b * b := by rw [add_sub]
    _ = a * a - a * b + a * b - b * b := by rw [mul_comm b a]
    _ = a * a - (a * b - a * b) - b * b := by rw [sub_add]
    _ = a * a - 0 - b * b := by rw [sub_self]
    _ = a * a - b * b := by rw [sub_zero]
    _ = a ^ 2 - b * b := by rw [pow_two a]
    _ = a ^ 2 - b ^ 2 := by rw [pow_two b]
