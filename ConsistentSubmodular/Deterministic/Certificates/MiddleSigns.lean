module

public import Mathlib

@[expose] public section

/-! Exact Bernstein certificates for the middle-rollback polynomial signs. -/

namespace ConsistentSubmodular

private theorem cubic_positive (t c₀ c₁ c₂ c₃ : ℝ)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) (h₀ : 0 < c₀) (h₁ : 0 < c₁)
    (h₂ : 0 < c₂) (h₃ : 0 < c₃) :
    0 < c₀ * (1 - t) ^ 3 + 3 * c₁ * t * (1 - t) ^ 2 +
      3 * c₂ * t ^ 2 * (1 - t) + c₃ * t ^ 3 := by
  by_cases htlt : t < 1
  · have hs : 0 < 1 - t := sub_pos.mpr htlt
    positivity
  · have heq : t = 1 := by linarith
    simp [heq, h₃]

private theorem quartic_positive (t c₀ c₁ c₂ c₃ c₄ : ℝ)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) (h₀ : 0 < c₀) (h₁ : 0 < c₁)
    (h₂ : 0 < c₂) (h₃ : 0 < c₃) (h₄ : 0 < c₄) :
    0 < c₀ * (1 - t) ^ 4 + 4 * c₁ * t * (1 - t) ^ 3 +
      6 * c₂ * t ^ 2 * (1 - t) ^ 2 + 4 * c₃ * t ^ 3 * (1 - t) + c₄ * t ^ 4 := by
  by_cases htlt : t < 1
  · have hs : 0 < 1 - t := sub_pos.mpr htlt
    positivity
  · have heq : t = 1 := by linarith
    simp [heq, h₄]

theorem middle_sign_u_H (k : ℝ) (hl : (38 / 23 : ℝ) ≤ k) (hu : k ≤ (7 / 4 : ℝ)) :
    0 < k ^ 3 + 4 * k ^ 2 - 51 * k + 72 := by
  let t := (k - (38 / 23 : ℝ)) / (9 / 92 : ℝ)
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have ht1 : t ≤ 1 := by dsimp [t]; linarith
  have hid : k ^ 3 + 4 * k ^ 2 - 51 * k + 72 =
      (38542 / 12167 : ℝ) * (1 - t) ^ 3 +
      3 * (4661 / 2116 : ℝ) * t * (1 - t) ^ 2 +
      3 * (233 / 184 : ℝ) * t ^ 2 * (1 - t) +
      (23 / 64 : ℝ) * t ^ 3 := by
    dsimp [t]
    ring
  rw [hid]
  exact cubic_positive t (38542 / 12167 : ℝ) (4661 / 2116 : ℝ) (233 / 184 : ℝ) (23 / 64 : ℝ) ht ht1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem middle_sign_u_Q (k : ℝ) (hl : (38 / 23 : ℝ) ≤ k) (hu : k ≤ (7 / 4 : ℝ)) :
    0 < -k ^ 3 - 19 * k ^ 2 + 134 * k - 144 := by
  let t := (k - (38 / 23 : ℝ)) / (9 / 92 : ℝ)
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have ht1 : t ≤ 1 := by dsimp [t]; linarith
  have hid : -k ^ 3 - 19 * k ^ 2 + 134 * k - 144 =
      (255720 / 12167 : ℝ) * (1 - t) ^ 3 +
      3 * (24411 / 1058 : ℝ) * t * (1 - t) ^ 2 +
      3 * (9219 / 368 : ℝ) * t ^ 2 * (1 - t) +
      (1725 / 64 : ℝ) * t ^ 3 := by
    dsimp [t]
    ring
  rw [hid]
  exact cubic_positive t (255720 / 12167 : ℝ) (24411 / 1058 : ℝ) (9219 / 368 : ℝ) (1725 / 64 : ℝ) ht ht1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem middle_sign_u_T (k : ℝ) (hl : (38 / 23 : ℝ) ≤ k) (hu : k ≤ (7 / 4 : ℝ)) :
    0 < -7 * k ^ 3 + 187 * k ^ 2 - 822 * k + 912 := by
  let t := (k - (38 / 23 : ℝ)) / (9 / 92 : ℝ)
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have ht1 : t ≤ 1 := by dsimp [t]; linarith
  have hid : -7 * k ^ 3 + 187 * k ^ 2 - 822 * k + 912 =
      (399000 / 12167 : ℝ) * (1 - t) ^ 3 +
      3 * (25677 / 1058 : ℝ) * t * (1 - t) ^ 2 +
      3 * (5973 / 368 : ℝ) * t ^ 2 * (1 - t) +
      (555 / 64 : ℝ) * t ^ 3 := by
    dsimp [t]
    ring
  rw [hid]
  exact cubic_positive t (399000 / 12167 : ℝ) (25677 / 1058 : ℝ) (5973 / 368 : ℝ) (555 / 64 : ℝ) ht ht1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem middle_sign_u_G1 (k : ℝ) (hl : (7 / 4 : ℝ) ≤ k) (hu : k ≤ 2) :
    0 < -3 * k ^ 3 - 42 * k ^ 2 + 319 * k - 360 := by
  let t := (k - (7 / 4 : ℝ)) / (1 / 4 : ℝ)
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have ht1 : t ≤ 1 := by dsimp [t]; linarith
  have hid : -3 * k ^ 3 - 42 * k ^ 2 + 319 * k - 360 =
      (3427 / 64 : ℝ) * (1 - t) ^ 3 +
      3 * (787 / 12 : ℝ) * t * (1 - t) ^ 2 +
      3 * (917 / 12 : ℝ) * t ^ 2 * (1 - t) +
      86 * t ^ 3 := by
    dsimp [t]
    ring
  rw [hid]
  exact cubic_positive t (3427 / 64 : ℝ) (787 / 12 : ℝ) (917 / 12 : ℝ) 86 ht ht1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem middle_sign_u_G2 (k : ℝ) (hl : (7 / 4 : ℝ) ≤ k) (hu : k ≤ 2) :
    0 < -3 * k ^ 3 - 27 * k ^ 2 + 236 * k - 288 := by
  let t := (k - (7 / 4 : ℝ)) / (1 / 4 : ℝ)
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have ht1 : t ≤ 1 := by dsimp [t]; linarith
  have hid : -3 * k ^ 3 - 27 * k ^ 2 + 236 * k - 288 =
      (1679 / 64 : ℝ) * (1 - t) ^ 3 +
      3 * (1715 / 48 : ℝ) * t * (1 - t) ^ 2 +
      3 * (133 / 3 : ℝ) * t ^ 2 * (1 - t) +
      52 * t ^ 3 := by
    dsimp [t]
    ring
  rw [hid]
  exact cubic_positive t (1679 / 64 : ℝ) (1715 / 48 : ℝ) (133 / 3 : ℝ) 52 ht ht1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem middle_sign_u_F1 (k : ℝ) (hl : (7 / 4 : ℝ) ≤ k) (hu : k ≤ 2) :
    0 < k ^ 3 + 69 * k ^ 2 - 252 * k + 225 := by
  let t := (k - (7 / 4 : ℝ)) / (1 / 4 : ℝ)
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have ht1 : t ≤ 1 := by dsimp [t]; linarith
  have hid : k ^ 3 + 69 * k ^ 2 - 252 * k + 225 =
      (43 / 64 : ℝ) * (1 - t) ^ 3 +
      3 * (9 / 16 : ℝ) * t * (1 - t) ^ 2 +
      3 * 2 * t ^ 2 * (1 - t) +
      5 * t ^ 3 := by
    dsimp [t]
    ring
  rw [hid]
  exact cubic_positive t (43 / 64 : ℝ) (9 / 16 : ℝ) 2 5 ht ht1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem middle_sign_u_F2 (k : ℝ) (hl : (7 / 4 : ℝ) ≤ k) (hu : k ≤ 2) :
    0 < k ^ 3 + 39 * k ^ 2 - 153 * k + 144 := by
  let t := (k - (7 / 4 : ℝ)) / (1 / 4 : ℝ)
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have ht1 : t ≤ 1 := by dsimp [t]; linarith
  have hid : k ^ 3 + 39 * k ^ 2 - 153 * k + 144 =
      (67 / 64 : ℝ) * (1 - t) ^ 3 +
      3 * (7 / 16 : ℝ) * t * (1 - t) ^ 2 +
      3 * (3 / 4 : ℝ) * t ^ 2 * (1 - t) +
      2 * t ^ 3 := by
    dsimp [t]
    ring
  rw [hid]
  exact cubic_positive t (67 / 64 : ℝ) (7 / 16 : ℝ) (3 / 4 : ℝ) 2 ht ht1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem middle_sign_z_Nplus (k : ℝ) (hl : (4 / 3 : ℝ) ≤ k) (hu : k ≤ (7 / 4 : ℝ)) :
    0 < 118 * k ^ 3 - 695 * k ^ 2 + 1081 * k - 378 := by
  let t := (k - (4 / 3 : ℝ)) / (5 / 12 : ℝ)
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have ht1 : t ≤ 1 := by dsimp [t]; linarith
  have hid : 118 * k ^ 3 - 695 * k ^ 2 + 1081 * k - 378 =
      (2902 / 27 : ℝ) * (1 - t) ^ 3 +
      3 * (9463 / 108 : ℝ) * t * (1 - t) ^ 2 +
      3 * (2633 / 48 : ℝ) * t ^ 2 * (1 - t) +
      (567 / 32 : ℝ) * t ^ 3 := by
    dsimp [t]
    ring
  rw [hid]
  exact cubic_positive t (2902 / 27 : ℝ) (9463 / 108 : ℝ) (2633 / 48 : ℝ) (567 / 32 : ℝ) ht ht1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem middle_sign_z_Nminus (k : ℝ) (hl : (4 / 3 : ℝ) ≤ k) (hu : k ≤ (7 / 4 : ℝ)) :
    0 < -160 * k ^ 4 + 1196 * k ^ 3 - 2494 * k ^ 2 + 702 * k + 1512 := by
  let t := (k - (4 / 3 : ℝ)) / (5 / 12 : ℝ)
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have ht1 : t ≤ 1 := by dsimp [t]; linarith
  have hid : -160 * k ^ 4 + 1196 * k ^ 3 - 2494 * k ^ 2 + 702 * k + 1512 =
      (27824 / 81 : ℝ) * (1 - t) ^ 4 +
      4 * (49739 / 216 : ℝ) * t * (1 - t) ^ 3 +
      6 * (57853 / 432 : ℝ) * t ^ 2 * (1 - t) ^ 2 +
      4 * (3881 / 64 : ℝ) * t ^ 3 * (1 - t) +
      (189 / 16 : ℝ) * t ^ 4 := by
    dsimp [t]
    ring
  rw [hid]
  exact quartic_positive t (27824 / 81 : ℝ) (49739 / 216 : ℝ) (57853 / 432 : ℝ) (3881 / 64 : ℝ) (189 / 16 : ℝ) ht ht1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem middle_sign_z_G1 (k : ℝ) (hl : (7 / 4 : ℝ) ≤ k) (hu : k ≤ 2) :
    0 < -14 * k ^ 3 + 33 * k ^ 2 + 164 * k - 171 := by
  let t := (k - (7 / 4 : ℝ)) / (1 / 4 : ℝ)
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have ht1 : t ≤ 1 := by dsimp [t]; linarith
  have hid : -14 * k ^ 3 + 33 * k ^ 2 + 164 * k - 171 =
      (4545 / 32 : ℝ) * (1 - t) ^ 3 +
      3 * (7421 / 48 : ℝ) * t * (1 - t) ^ 2 +
      3 * (499 / 3 : ℝ) * t ^ 2 * (1 - t) +
      177 * t ^ 3 := by
    dsimp [t]
    ring
  rw [hid]
  exact cubic_positive t (4545 / 32 : ℝ) (7421 / 48 : ℝ) (499 / 3 : ℝ) 177 ht ht1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem middle_sign_z_G2 (k : ℝ) (hl : (7 / 4 : ℝ) ≤ k) (hu : k ≤ 2) :
    0 < -10 * k ^ 3 + 21 * k ^ 2 + 139 * k - 180 := by
  let t := (k - (7 / 4 : ℝ)) / (1 / 4 : ℝ)
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have ht1 : t ≤ 1 := by dsimp [t]; linarith
  have hid : -10 * k ^ 3 + 21 * k ^ 2 + 139 * k - 180 =
      (2367 / 32 : ℝ) * (1 - t) ^ 3 +
      3 * (4033 / 48 : ℝ) * t * (1 - t) ^ 2 +
      3 * (1121 / 12 : ℝ) * t ^ 2 * (1 - t) +
      102 * t ^ 3 := by
    dsimp [t]
    ring
  rw [hid]
  exact cubic_positive t (2367 / 32 : ℝ) (4033 / 48 : ℝ) (1121 / 12 : ℝ) 102 ht ht1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem middle_sign_z_F1 (k : ℝ) (hl : (7 / 4 : ℝ) ≤ k) (hu : k ≤ 2) :
    0 < 35 * k ^ 3 - 104 * k ^ 2 + 60 * k + 27 := by
  let t := (k - (7 / 4 : ℝ)) / (1 / 4 : ℝ)
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have ht1 : t ≤ 1 := by dsimp [t]; linarith
  have hid : 35 * k ^ 3 - 104 * k ^ 2 + 60 * k + 27 =
      (69 / 64 : ℝ) * (1 - t) ^ 3 +
      3 * (61 / 24 : ℝ) * t * (1 - t) ^ 2 +
      3 * (17 / 3 : ℝ) * t ^ 2 * (1 - t) +
      11 * t ^ 3 := by
    dsimp [t]
    ring
  rw [hid]
  exact cubic_positive t (69 / 64 : ℝ) (61 / 24 : ℝ) (17 / 3 : ℝ) 11 ht ht1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem middle_sign_z_F2 (k : ℝ) (hl : (7 / 4 : ℝ) ≤ k) (hu : k ≤ 2) :
    0 < 20 * k ^ 3 - 62 * k ^ 2 + 33 * k + 27 := by
  let t := (k - (7 / 4 : ℝ)) / (1 / 4 : ℝ)
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have ht1 : t ≤ 1 := by dsimp [t]; linarith
  have hid : 20 * k ^ 3 - 62 * k ^ 2 + 33 * k + 27 =
      (33 / 16 : ℝ) * (1 - t) ^ 3 +
      3 * (49 / 24 : ℝ) * t * (1 - t) ^ 2 +
      3 * (35 / 12 : ℝ) * t ^ 2 * (1 - t) +
      5 * t ^ 3 := by
    dsimp [t]
    ring
  rw [hid]
  exact cubic_positive t (33 / 16 : ℝ) (49 / 24 : ℝ) (35 / 12 : ℝ) 5 ht ht1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end ConsistentSubmodular
