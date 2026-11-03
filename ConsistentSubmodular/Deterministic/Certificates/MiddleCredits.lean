module

public import ConsistentSubmodular.Deterministic.Certificates.MiddleSources
public import ConsistentSubmodular.Deterministic.Certificates.MiddleSigns

@[expose] public section

/-! Positive first and third scalar credits for middle-parameter rollback. -/

noncomputable section
namespace ConsistentSubmodular

def middleCap (k d₀ : ℝ) : ℝ := 2 - 3 / k + 3 * (4 - k) * d₀ / k
def middleI (k d₀ d p : ℝ) : ℝ := (3 - k) * p - k * d - 2 * (4 - k) * d₀
def middleU (k d₀ d p : ℝ) : ℝ := d - 2 * middleCap k d₀ + 3 * p -
  (3 - k) * ((p + k * d + (4 - k) * d₀) / (4 - k))
def middleT (k d₀ d p : ℝ) : ℝ :=
  (13 - (k - 2) ^ 2) * p + (16 + 5 * (k - 2) ^ 2) * d -
    (4 - k) * (27 - k - 2 * k ^ 2) * d₀ - 2 * k * (4 - k) * (k - 1)

theorem middle_U_lower (k d₀ d p : ℝ)
    (hk : (38 : ℝ) / 23 ≤ k) (hk7 : k ≤ (7 : ℝ) / 4)
    (hd : (7 : ℝ) / 40 ≤ d) (hp : p ≤ 2 * d) (hI : 0 ≤ middleI k d₀ d p) :
    0 < middleU k d₀ d p := by
  have hk0 : 0 < k := by linarith
  have hk4 : 0 < 4 - k := by linarith
  have hA : 0 ≤ 24 - 3 * k - k ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ 2 - k by linarith) (show 0 ≤ 2 + k by linarith)]
  have hH := middle_sign_u_H k hk hk7
  have hQ := middle_sign_u_Q k hk hk7
  have hT := middle_sign_u_T k hk hk7
  have hid : 80 * k * (4 - k) * middleU k d₀ d p =
      40 * (24 - 3 * k - k ^ 2) * middleI k d₀ d p +
      40 * (k ^ 3 + 4 * k ^ 2 - 51 * k + 72) * (2 * d - p) +
      40 * (-k ^ 3 - 19 * k ^ 2 + 134 * k - 144) * (d - 7 / 40) +
      (-7 * k ^ 3 + 187 * k ^ 2 - 822 * k + 912) := by
    unfold middleU middleCap middleI
    field_simp
    ring
  have hpositive : 0 < 80 * k * (4 - k) * middleU k d₀ d p := by
    rw [hid]
    have hpd : 0 ≤ 2 * d - p := sub_nonneg.mpr hp
    have hdd : 0 ≤ d - 7 / 40 := sub_nonneg.mpr hd
    positivity
  exact (mul_pos_iff_of_pos_left (by positivity : 0 < 80 * k * (4 - k))).mp hpositive

theorem middle_U_upper_first (k d₀ d p : ℝ)
    (hk : (7 : ℝ) / 4 ≤ k) (hk2 : k ≤ 2) (hd₀ : 0 ≤ d₀)
    (hI : 0 ≤ middleI k d₀ d p) (hline : 2 / 25 + 2 * p / 5 ≤ d) :
    0 < middleU k d₀ d p := by
  have hk0 : 0 < k := by linarith
  have hk4 : 0 < 4 - k := by linarith
  have hden : 0 < 15 - 7 * k := by linarith
  have hA : 0 ≤ 2 * k ^ 2 - 18 * k + 53 := by nlinarith [sq_nonneg k]
  have hB : 0 < k ^ 2 - k + 3 := by nlinarith [sq_nonneg (k - 1 / 2)]
  have hG := middle_sign_u_G1 k hk hk2
  have hF := middle_sign_u_F1 k hk hk2
  have hid : k * (4 - k) * (15 - 7 * k) * middleU k d₀ d p =
      k * (2 * k ^ 2 - 18 * k + 53) * middleI k d₀ d p +
      5 * k * (4 - k) * (k ^ 2 - k + 3) * (d - 2 / 25 - 2 * p / 5) +
      (4 - k) * (-3 * k ^ 3 - 42 * k ^ 2 + 319 * k - 360) * d₀ +
      (2 / 5 : ℝ) * (4 - k) * (k ^ 3 + 69 * k ^ 2 - 252 * k + 225) := by
    unfold middleU middleCap middleI
    field_simp
    ring
  have hpositive : 0 < k * (4 - k) * (15 - 7 * k) * middleU k d₀ d p := by
    rw [hid]
    have hl : 0 ≤ d - 2 / 25 - 2 * p / 5 := by linarith
    positivity
  exact (mul_pos_iff_of_pos_left (by positivity : 0 < k * (4 - k) * (15 - 7 * k))).mp hpositive

theorem middle_U_upper_second (k d₀ d p : ℝ)
    (hk : (7 : ℝ) / 4 ≤ k) (hk2 : k ≤ 2) (hd₀ : 0 ≤ d₀)
    (hI : 0 ≤ middleI k d₀ d p) (hline : 1 / 8 + p / 4 ≤ d) :
    0 < middleU k d₀ d p := by
  have hk0 : 0 < k := by linarith
  have hk4 : 0 < 4 - k := by linarith
  have hden : 0 < 12 - 5 * k := by linarith
  have hA : 0 ≤ k ^ 2 - 12 * k + 40 := by nlinarith [sq_nonneg k]
  have hB : 0 < k ^ 2 - k + 3 := by nlinarith [sq_nonneg (k - 1 / 2)]
  have hG := middle_sign_u_G2 k hk hk2
  have hF := middle_sign_u_F2 k hk hk2
  have hid : k * (4 - k) * (12 - 5 * k) * middleU k d₀ d p =
      k * (k ^ 2 - 12 * k + 40) * middleI k d₀ d p +
      4 * k * (4 - k) * (k ^ 2 - k + 3) * (d - 1 / 8 - p / 4) +
      (4 - k) * (-3 * k ^ 3 - 27 * k ^ 2 + 236 * k - 288) * d₀ +
      (1 / 2 : ℝ) * (4 - k) * (k ^ 3 + 39 * k ^ 2 - 153 * k + 144) := by
    unfold middleU middleCap middleI
    field_simp
    ring
  have hpositive : 0 < k * (4 - k) * (12 - 5 * k) * middleU k d₀ d p := by
    rw [hid]
    have hl : 0 ≤ d - 1 / 8 - p / 4 := by linarith
    positivity
  exact (mul_pos_iff_of_pos_left (by positivity : 0 < k * (4 - k) * (12 - 5 * k))).mp hpositive

theorem middle_T_lower (k d₀ d p : ℝ)
    (hk : (4 : ℝ) / 3 ≤ k) (hk7 : k ≤ (7 : ℝ) / 4) (hd₀ : 0 ≤ d₀)
    (hd : (7 : ℝ) / 40 ≤ d) (hp : p ≤ 2 * d) (hI : 0 ≤ middleI k d₀ d p) :
    0 < middleT k d₀ d p := by
  let Q := 27 - k - 2 * k ^ 2
  let H := 2 * k ^ 3 - 3 * k ^ 2 - 38 * k + 63
  let D := -2 * k ^ 3 + 9 * k ^ 2 - 13 * k + 72
  have hk0 : 0 < k := by linarith
  have hk3 : 0 < 3 - k := by linarith
  have hk4 : 0 < 4 - k := by linarith
  have hk1 : 0 ≤ k - 1 := by linarith
  have hQ : 0 ≤ Q := by
    dsimp [Q]
    nlinarith [mul_nonneg (show 0 ≤ 2 - k by linarith) (show 0 ≤ 2 + k by linarith)]
  have hNp := middle_sign_z_Nplus k hk hk7
  have hNm := middle_sign_z_Nminus k hk hk7
  have hproduct : 0 ≤ 160 * k * (4 - k) * (k - 1) := by positivity
  have hD2H : 0 < D - 2 * H := by
    dsimp [D, H]
    nlinarith only [hNp, hproduct]
  have hE : 0 < (3 - k) * D - k * H := by
    have hprod := mul_nonneg hk3.le hproduct
    dsimp [D, H]
    nlinarith only [hNm, hprod]
  have hdd : 0 ≤ d - 7 / 40 := sub_nonneg.mpr hd
  by_cases hH : 0 ≤ H
  · have hid : 2 * middleT k d₀ d p =
        Q * middleI k d₀ d p + H * (2 * d - p) + (D - 2 * H) * (d - 7 / 40) +
          (118 * k ^ 3 - 695 * k ^ 2 + 1081 * k - 378) / 40 := by
      dsimp [Q, H, D, middleI, middleT]
      ring
    have hpos : 0 < 2 * middleT k d₀ d p := by
      rw [hid]
      have hpd : 0 ≤ 2 * d - p := sub_nonneg.mpr hp
      positivity
    linarith
  · have hparent : 0 ≤ (3 - k) * p - k * d := by
      have := mul_nonneg (show 0 ≤ 2 * (4 - k) by linarith) hd₀
      unfold middleI at hI
      nlinarith
    have hid : 2 * (3 - k) * middleT k d₀ d p =
        (3 - k) * Q * middleI k d₀ d p - H * ((3 - k) * p - k * d) +
          ((3 - k) * D - k * H) * (d - 7 / 40) +
          (-160 * k ^ 4 + 1196 * k ^ 3 - 2494 * k ^ 2 + 702 * k + 1512) / 40 := by
      dsimp [Q, H, D, middleI, middleT]
      ring
    have hpos : 0 < 2 * (3 - k) * middleT k d₀ d p := by
      rw [hid]
      have hnegative : 0 ≤ -H := by linarith
      have hprod := mul_nonneg hnegative hparent
      have hfirst := mul_nonneg (mul_nonneg hk3.le hQ) hI
      have hthird := mul_nonneg hE.le hdd
      linarith
    exact (mul_pos_iff_of_pos_left (by positivity : 0 < 2 * (3 - k))).mp hpos

theorem middle_T_upper_first (k d₀ d p : ℝ)
    (hk : (7 : ℝ) / 4 ≤ k) (hk2 : k ≤ 2) (hd₀ : 0 ≤ d₀)
    (hI : 0 ≤ middleI k d₀ d p) (hline : 2 / 25 + 2 * p / 5 ≤ d) :
    0 < middleT k d₀ d p := by
  have hk4 : 0 < 4 - k := by linarith
  have hden : 0 < 15 - 7 * k := by linarith
  have hA : 0 ≤ 5 * k ^ 2 - 20 * k + 117 := by nlinarith [sq_nonneg (k - 2)]
  have hB : 0 < 2 * k ^ 2 - 5 * k + 9 := by nlinarith [sq_nonneg (k - 5 / 4)]
  have hG := middle_sign_z_G1 k hk hk2
  have hF := middle_sign_z_F1 k hk hk2
  have hid : (15 - 7 * k) * middleT k d₀ d p =
      (5 * k ^ 2 - 20 * k + 117) * middleI k d₀ d p +
      15 * (4 - k) * (2 * k ^ 2 - 5 * k + 9) * (d - 2 / 25 - 2 * p / 5) +
      (4 - k) * (-14 * k ^ 3 + 33 * k ^ 2 + 164 * k - 171) * d₀ +
      (2 / 5 : ℝ) * (4 - k) * (35 * k ^ 3 - 104 * k ^ 2 + 60 * k + 27) := by
    unfold middleT middleI
    ring
  have hpos : 0 < (15 - 7 * k) * middleT k d₀ d p := by
    rw [hid]
    have hl : 0 ≤ d - 2 / 25 - 2 * p / 5 := by linarith
    positivity
  exact (mul_pos_iff_of_pos_left hden).mp hpos

theorem middle_T_upper_second (k d₀ d p : ℝ)
    (hk : (7 : ℝ) / 4 ≤ k) (hk2 : k ≤ 2) (hd₀ : 0 ≤ d₀)
    (hI : 0 ≤ middleI k d₀ d p) (hline : 1 / 8 + p / 4 ≤ d) :
    0 < middleT k d₀ d p := by
  have hk4 : 0 < 4 - k := by linarith
  have hden : 0 < 12 - 5 * k := by linarith
  have hA : 0 ≤ k ^ 2 - 4 * k + 72 := by nlinarith [sq_nonneg (k - 2)]
  have hB : 0 < 2 * k ^ 2 - 5 * k + 9 := by nlinarith [sq_nonneg (k - 5 / 4)]
  have hG := middle_sign_z_G2 k hk hk2
  have hF := middle_sign_z_F2 k hk hk2
  have hid : (12 - 5 * k) * middleT k d₀ d p =
      (k ^ 2 - 4 * k + 72) * middleI k d₀ d p +
      12 * (4 - k) * (2 * k ^ 2 - 5 * k + 9) * (d - 1 / 8 - p / 4) +
      (4 - k) * (-10 * k ^ 3 + 21 * k ^ 2 + 139 * k - 180) * d₀ +
      (1 / 2 : ℝ) * (4 - k) * (20 * k ^ 3 - 62 * k ^ 2 + 33 * k + 27) := by
    unfold middleT middleI
    ring
  have hpos : 0 < (12 - 5 * k) * middleT k d₀ d p := by
    rw [hid]
    have hl : 0 ≤ d - 1 / 8 - p / 4 := by linarith
    positivity
  exact (mul_pos_iff_of_pos_left hden).mp hpos

theorem middle_U_positive (k d₀ d p q δ : ℝ)
    (hk : (4 : ℝ) / 3 ≤ k) (hk2 : k ≤ 2) (hd₀ : 0 ≤ d₀)
    (hd7 : (7 : ℝ) / 40 ≤ d) (hd4 : d ≤ 1 / 4) (hp : p ≤ 2 * d)
    (hI : 0 ≤ middleI k d₀ d p)
    (hparent : k * p ≤ 2 * k - 3 + 3 * (4 - k) * d₀)
    (hq1 : 1 ≤ q) (hq4 : q ≤ (4 : ℝ) / 3) (hδ : 0 ≤ δ)
    (hJ : 0 ≤ (36 - 25 * q + 3 * q ^ 2) * d - (3 - q) * (3 - 2 * q) -
      q * (4 - q) * p - q ^ 2 * δ) : 0 < middleU k d₀ d p := by
  have hcut := middle_parent_cutoff k d₀ d p hk hk2 hd7 hd4 hp hI hparent
  by_cases hk7 : k ≤ (7 : ℝ) / 4
  · exact middle_U_lower k d₀ d p hcut hk7 hd7 hp hI
  · have hk7' : (7 : ℝ) / 4 ≤ k := le_of_not_ge hk7
    have hpfloor := middle_parent_p_floor k d₀ d p hk7' hk2 hd7 hd₀ hI
    by_cases hp3 : p ≤ 3 / 10
    · exact middle_U_upper_first k d₀ d p hk7' hk2 hd₀ hI
        (middle_child_deficit_first q d p δ hq1 hq4 hδ (by linarith) hp3 hJ)
    · exact middle_U_upper_second k d₀ d p hk7' hk2 hd₀ hI
        (middle_child_deficit_second q d p δ hq1 hq4 hδ (le_of_not_ge hp3) (by linarith) hJ)

theorem middle_T_positive (k d₀ d p q δ : ℝ)
    (hk : (4 : ℝ) / 3 ≤ k) (hk2 : k ≤ 2) (hd₀ : 0 ≤ d₀)
    (hd7 : (7 : ℝ) / 40 ≤ d) (hd4 : d ≤ 1 / 4) (hp : p ≤ 2 * d)
    (hI : 0 ≤ middleI k d₀ d p)
    (hq1 : 1 ≤ q) (hq4 : q ≤ (4 : ℝ) / 3) (hδ : 0 ≤ δ)
    (hJ : 0 ≤ (36 - 25 * q + 3 * q ^ 2) * d - (3 - q) * (3 - 2 * q) -
      q * (4 - q) * p - q ^ 2 * δ) : 0 < middleT k d₀ d p := by
  by_cases hk7 : k ≤ (7 : ℝ) / 4
  · exact middle_T_lower k d₀ d p hk hk7 hd₀ hd7 hp hI
  · have hk7' : (7 : ℝ) / 4 ≤ k := le_of_not_ge hk7
    have hpfloor := middle_parent_p_floor k d₀ d p hk7' hk2 hd7 hd₀ hI
    by_cases hp3 : p ≤ 3 / 10
    · exact middle_T_upper_first k d₀ d p hk7' hk2 hd₀ hI
        (middle_child_deficit_first q d p δ hq1 hq4 hδ (by linarith) hp3 hJ)
    · exact middle_T_upper_second k d₀ d p hk7' hk2 hd₀ hI
        (middle_child_deficit_second q d p δ hq1 hq4 hδ (le_of_not_ge hp3) (by linarith) hJ)

theorem middle_Z_positive (k d₀ d p q δ P : ℝ)
    (hk : (4 : ℝ) / 3 ≤ k) (hk2 : k ≤ 2) (hd₀ : 0 ≤ d₀)
    (hd7 : (7 : ℝ) / 40 ≤ d) (hd4 : d ≤ 1 / 4) (hp : p ≤ 2 * d)
    (hI : 0 ≤ middleI k d₀ d p)
    (hq1 : 1 ≤ q) (hq4 : q ≤ (4 : ℝ) / 3) (hδ : 0 ≤ δ)
    (hJ : 0 ≤ (36 - 25 * q + 3 * q ^ 2) * d - (3 - q) * (3 - 2 * q) -
      q * (4 - q) * p - q ^ 2 * δ)
    (hLP : 0 ≤ 2 * P - 3 * p - 4 * d - δ)
    (hG : 0 ≤ k * (4 - k) * δ - p - (k - 2) ^ 2 * d + (4 - k) * (3 - k) * d₀) :
    0 < P - (k - 1) + (k - 2) ^ 2 * (d + δ) - (4 - k) ^ 2 * d₀ := by
  have hT := middle_T_positive k d₀ d p q δ hk hk2 hd₀ hd7 hd4 hp hI hq1 hq4 hδ hJ
  have hk0 : 0 < k := by linarith
  have hk4 : 0 < 4 - k := by linarith
  have hid : 2 * k * (4 - k) *
      (P - (k - 1) + (k - 2) ^ 2 * (d + δ) - (4 - k) ^ 2 * d₀) =
      middleT k d₀ d p + k * (4 - k) * (2 * P - 3 * p - 4 * d - δ) +
      (1 + 2 * (k - 2) ^ 2) *
        (k * (4 - k) * δ - p - (k - 2) ^ 2 * d + (4 - k) * (3 - k) * d₀) := by
    unfold middleT
    ring
  have h1 := mul_nonneg (mul_nonneg hk0.le hk4.le) hLP
  have h2 := mul_nonneg (show 0 ≤ 1 + 2 * (k - 2) ^ 2 by positivity) hG
  have hpositive : 0 < 2 * k * (4 - k) *
      (P - (k - 1) + (k - 2) ^ 2 * (d + δ) - (4 - k) ^ 2 * d₀) := by
    linarith only [hid, hT, h1, h2]
  exact (mul_pos_iff_of_pos_left (by positivity : 0 < 2 * k * (4 - k))).mp hpositive

/-- The three scalar credits from precisely the parent/child source rows. -/
theorem middle_three_credits (k d₀ d p W q δ w P : ℝ)
    (hk : (4 : ℝ) / 3 ≤ k) (hk2 : k ≤ 2) (hd₀ : 0 ≤ d₀)
    (hd7 : (7 : ℝ) / 40 ≤ d) (hd4 : d ≤ 1 / 4) (hpd : d ≤ p) (hp : p ≤ 2 * d)
    (hparentatt : p = (4 - k) * W - k * d - (4 - k) * d₀)
    (hparentper : W + d₀ ≤ p)
    (hparent : k * p ≤ 2 * k - 3 + 3 * (4 - k) * d₀)
    (hq1 : 1 ≤ q) (hq4 : q ≤ (4 : ℝ) / 3) (hδ : 0 ≤ δ)
    (hatt : P = (4 - q) * w - q * δ - 4 * d) (hper : p + w ≤ P)
    (hcap : w ≤ 1 - d - δ) (hfailed : 0 ≤ q * (2 - 3 * d - P) - 3 * (1 - 4 * d))
    (hG : 0 ≤ k * (4 - k) * δ - p - (k - 2) ^ 2 * d + (4 - k) * (3 - k) * d₀) :
    0 < d - 2 * middleCap k d₀ + 3 * p - (3 - k) * W ∧
    0 ≤ p + (3 - 2 * k) * (d + δ) - 2 * (4 - k) * d₀ ∧
    0 < P - (k - 1) + (k - 2) ^ 2 * (d + δ) - (4 - k) ^ 2 * d₀ := by
  have hI := middle_parent_I k d₀ d p W (by linarith) hparentatt hparentper
  have hF := middle_child_elimination q d p δ w P (by linarith) hatt hper
  have hK := middle_child_capacity q d p δ w P (by linarith) hatt hper hcap
  have hJ := middle_child_credit_combination q d p δ P (by linarith) (by linarith) hF hfailed
  have hδd := middle_child_delta_bound q d p δ hq1 hq4 (by linarith) hpd hK hJ
  have hcut := middle_parent_cutoff k d₀ d p hk hk2 hd7 hd4 hp hI hparent
  have hLP := middle_child_benchmark_floor q d p δ P hq1 (by linarith) (by linarith)
    (by linarith) hδ hF
  have hU := middle_U_positive k d₀ d p q δ hk hk2 hd₀ hd7 hd4 hp hI hparent hq1 hq4 hδ hJ
  have hW : W = (p + k * d + (4 - k) * d₀) / (4 - k) := by
    apply (eq_div_iff (show 4 - k ≠ 0 by linarith)).2
    nlinarith only [hparentatt]
  refine ⟨?_, middle_credit_V k d₀ d p δ (by linarith) hk2 (by linarith) hp hδd hI,
    middle_Z_positive k d₀ d p q δ P hk hk2 hd₀ hd7 hd4 hp hI hq1 hq4 hδ hJ hLP hG⟩
  rw [hW]
  exact hU

end ConsistentSubmodular
