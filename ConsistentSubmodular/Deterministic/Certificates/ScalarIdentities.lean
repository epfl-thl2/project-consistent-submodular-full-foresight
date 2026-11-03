module

public import Mathlib

@[expose] public section

/-! Scalar identities and one inequality used by the constructors and exits. -/

namespace ConsistentSubmodular

variable (H P c α β L G R y A δ w q d d₀ kpar u z T Pt g a η n b : ℝ)

theorem exit_square_identity :
    4 * R * (L + (1 - y) ^ 2 * R + y * G - (3 : ℝ) / 4 * (L + G)) =
      (2 * R * (1 - y) - G) ^ 2 + R * (L + G) - G ^ 2 := by
  ring

theorem eligibility_gap_identity :
    (4 * A - 3 - q * δ - (q - q ^ 2 / 4) * (A - δ - w)) -
      (w - (q - 1) * δ - 3 * (1 - A)) =
      (1 - (q - q ^ 2 / 4)) * (A - δ - w) := by
  ring

theorem quadratic_overlap_bound (x : ℝ) : x * (1 - x) ≤ (1 : ℝ) / 4 := by
  nlinarith [sq_nonneg (x - (1 : ℝ) / 2)]

end ConsistentSubmodular
