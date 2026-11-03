module

public import ConsistentSubmodular.Deterministic.Certificates.RelayError

@[expose] public section

/-! The high-anchor relay, the fact for `A ≥ 33/40` in
`docs/three_quarter_certificate.pdf`, with explicit polynomial sign
certificates. -/

namespace ConsistentSubmodular

theorem high_anchor_eligibility_polynomial (q p d : ℝ)
    (hq1 : 1 ≤ q) (hq2 : q ≤ 2) (hd : 0 ≤ d) (hd7 : d ≤ 7 / 40)
    (hpd : d ≤ p) :
    0 ≤ (3 - q) * (q - 2) ^ 2 + q * (4 - q) * p +
      (q ^ 3 - 11 * q ^ 2 + 44 * q - 48) * d := by
  let K := q ^ 3 - 12 * q ^ 2 + 48 * q - 48
  have hq : 0 ≤ q := by linarith
  have h4 : 0 ≤ 4 - q := by linarith
  have hC := mul_nonneg (show 0 ≤ 3 - q by linarith) (sq_nonneg (q - 2))
  have hpdterm := mul_nonneg (mul_nonneg hq h4) (sub_nonneg.mpr hpd)
  by_cases hK : 0 ≤ K
  · have := mul_nonneg hK hd
    dsimp [K] at this
    nlinarith only [hC, hpdterm, this]
  · have hqlow : q ≤ 3 / 2 := by
      by_contra hn
      have hs : 0 ≤ q - 3 / 2 := by linarith
      have hf : 0 ≤ q ^ 2 - (21 / 2 : ℝ) * q + 129 / 4 := by
        nlinarith [sq_nonneg q]
      have hp := mul_nonneg hs hf
      dsimp [K] at hK
      nlinarith
    let t := 2 * (q - 1)
    have ht : 0 ≤ t := by dsimp [t]; linarith
    have ht1 : 0 ≤ 1 - t := by dsimp [t]; linarith
    have hid : (3 - q) * (q - 2) ^ 2 + K * (7 / 40) =
        (3 / 40 : ℝ) * (1 - t) ^ 3 + (7 / 80 : ℝ) * t * (1 - t) ^ 2 +
        (89 / 160 : ℝ) * t ^ 2 * (1 - t) + (141 / 320 : ℝ) * t ^ 3 := by
      dsimp [K, t]
      ring
    have hpoly : 0 ≤ (3 - q) * (q - 2) ^ 2 + K * (7 / 40) := by
      rw [hid]
      positivity
    have hdk := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hd7) (le_of_not_ge hK)
    dsimp [K] at *
    nlinarith only [hpoly, hdk, hpdterm]

/-- At high anchors every attaining stage is actually eligible. -/
theorem high_anchor_attainer_eligible (q p d δ w b : ℝ)
    (hq1 : 1 ≤ q) (hq2 : q ≤ 2) (hd : 0 ≤ d) (hd7 : d ≤ 7 / 40)
    (hpd : d ≤ p) (hδ : 0 ≤ δ) (hb : p + d ≤ b)
    (hatt : (3 - q) * w = q * δ + b + 3 * d) :
    0 ≤ 1 - 4 * d - q * δ - (q - q ^ 2 / 4) * (1 - d - δ - w) := by
  have hF := high_anchor_eligibility_polynomial q p d hq1 hq2 hd hd7 hpd
  have h1 := mul_nonneg (sq_nonneg q) hδ
  have h2 := mul_nonneg (mul_nonneg (show 0 ≤ q by linarith)
    (show 0 ≤ 4 - q by linarith)) (sub_nonneg.mpr hb)
  have hh := congrArg (fun x : ℝ => q * (4 - q) * x) hatt
  have hid : 4 * (3 - q) *
      (1 - 4 * d - q * δ - (q - q ^ 2 / 4) * (1 - d - δ - w)) =
      ((3 - q) * (q - 2) ^ 2 + q * (4 - q) * p +
        (q ^ 3 - 11 * q ^ 2 + 44 * q - 48) * d) +
        q ^ 2 * δ + q * (4 - q) * (b - (p + d)) := by
    nlinarith only [hh]
  have hpos : 0 < 4 * (3 - q) := by linarith
  nlinarith only [hF, h1, h2, hid, hpos]

theorem high_anchor_cubic_nonpositive (p : ℝ) (hp : 0 ≤ p) (hp9 : p ≤ 9 / 40) :
    6 * p ^ 3 - 13 * p ^ 2 + 7 * p - 1 ≤ 0 := by
  let t := 40 * p / 9
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hs : 0 ≤ 1 - t := by dsimp [t]; linarith
  have hid : 6 * p ^ 3 - 13 * p ^ 2 + 7 * p - 1 =
      -((1 - t) ^ 3 + (57 / 40 : ℝ) * t * (1 - t) ^ 2 +
        (813 / 1600 : ℝ) * t ^ 2 * (1 - t) + (473 / 32000 : ℝ) * t ^ 3) := by
    dsimp [t]
    ring
  rw [hid]
  have : 0 ≤ (1 - t) ^ 3 + (57 / 40 : ℝ) * t * (1 - t) ^ 2 +
      (813 / 1600 : ℝ) * t ^ 2 * (1 - t) + (473 / 32000 : ℝ) * t ^ 3 := by positivity
  linarith

theorem high_anchor_low_baseline_error (d p : ℝ)
    (hd : 0 ≤ d) (hd7 : d ≤ 7 / 40) (hp : 0 ≤ p) (hp2d : p ≤ 2 * d)
    (hcredit : d ≤ p * (1 - p)) :
    relayError (1 - d) (3 * d) (p + d) (3 * d) ≤ 0 := by
  by_cases hp9 : p ≤ 9 / 40
  · have hp1 : 0 ≤ 1 - p := by linarith
    have hcoef : 0 ≤ p + 1 + 6 * (p * (1 - p) + d) := by positivity
    have hinc := mul_nonneg (sub_nonneg.mpr hcredit) hcoef
    have hpoly := mul_nonpos_of_nonneg_of_nonpos hp (high_anchor_cubic_nonpositive p hp hp9)
    unfold relayError
    nlinarith only [hinc, hpoly]
  · have hpoly : p ^ 2 - (73 / 40 : ℝ) * p + 287 / 800 ≤ 0 := by
      have h := quadratic_nonpositive_between (-(73 / 40 : ℝ)) (287 / 800)
        (9 / 40) (7 / 20) p (by linarith) (by linarith) (by norm_num) (by norm_num)
      nlinarith only [h]
    have hcoef : 0 ≤ p + 1 + 6 * (7 / 40 + d) := by positivity
    have hinc := mul_nonneg (sub_nonneg.mpr hd7) hcoef
    unfold relayError
    nlinarith only [hinc, hpoly]

/-- Failed high-anchor credit forces the attaining residual gap beyond the
deficit budget. Since `q < 3` and `b + 3 d > 0`, the attaining equation
`(3 - q) w = q δ + b + 3 d` makes `w` positive. The proof clears every
denominator before comparing slopes. -/
theorem high_anchor_gap (d p δ w b q : ℝ)
    (hd : 0 < d) (hd7 : d ≤ 7 / 40) (hp : 0 ≤ p)
    (hcredit : (1 : ℝ) / 2 ≤ p ∨ d ≤ p * (1 - p))
    (hδ : 0 ≤ δ) (hb : p + d ≤ b) (hq1 : 1 ≤ q) (hq3 : q < 3)
    (hatt : q * (δ + w) = 3 * w - b - 3 * d)
    (hfail : 3 * (1 - 4 * d) < (2 * (1 - d) - b - w) * q) :
    3 * d < w := by
  let A := 1 - d
  let D := 3 * d
  let L := p + d
  let B := 1 - 4 * d
  let F := fun b w : ℝ => (2 * A - b - w) * (3 * w - b - D)
  have hD : 0 < D := by dsimp [D]; positivity
  have hB : 0 < B := by dsimp [B]; linarith
  have hq : 0 < q := by linarith
  have hL : 2 * d ≤ L := by
    dsimp [L]
    rcases hcredit with h | h
    · linarith
    · nlinarith [sq_nonneg p]
  have hLB : L ≤ b := hb
  have hb0 : 0 ≤ b := by dsimp [L] at hLB; linarith
  have hw : 0 < w := by
    have hqδ := mul_nonneg hq.le hδ
    have hscaled : 0 < (3 - q) * w := by nlinarith only [hatt, hqδ, hb0, hd]
    exact (mul_pos_iff_of_pos_left (sub_pos.mpr hq3)).mp hscaled
  have hpos : 0 < 2 * A - b - w := by
    by_contra hn
    have := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hn) hq.le
    dsimp [A] at *
    linarith
  have hbound : b + D ≤ 2 * w := by
    have h1 := mul_nonneg (sub_nonneg.mpr hq1) hw.le
    have h2 := mul_nonneg hq.le hδ
    dsimp [D]
    nlinarith
  have hfailed : 3 * B * w < F b w := by
    have h1 := mul_lt_mul_of_pos_right hfail hw
    have h2 := mul_nonneg (mul_nonneg hpos.le hq.le) hδ
    have heq := congrArg (fun x : ℝ => (2 * A - b - w) * x) hatt
    dsimp [A, B, D, F] at *
    nlinarith only [h1, h2, heq]
  by_contra hn
  have hwD : w ≤ D := le_of_not_gt hn
  have hbD : b ≤ D := by linarith
  have hLD : L ≤ D := hLB.trans hbD
  have hstrong : d ≤ p * (1 - p) := by
    rcases hcredit with h | h
    · dsimp [L, D] at hLD
      linarith
    · exact h
  have he := high_anchor_low_baseline_error d p hd.le hd7 hp
    (by dsimp [L, D] at hLD; linarith) hstrong
  have hcompare : F b w ≤ F L w := by
    have hfactor : 0 ≤ 2 * w + 2 * A - D - b - L := by
      dsimp [A, D] at *
      linarith
    have := mul_nonneg (sub_nonneg.mpr hLB) hfactor
    dsimp [F]
    nlinarith only [this]
  have hinner : 0 ≤ (2 * A - L) * (L + D) - 3 * D * w := by
    have h1 := mul_nonneg hd.le (show 0 ≤ 10 - 47 * d by linarith)
    have h2 := mul_nonneg (sub_nonneg.mpr hL)
      (show 0 ≤ 2 - 7 * d - L by dsimp [L, D] at hLD; dsimp [L]; linarith)
    have h3 := mul_nonneg (show 0 ≤ 3 * D by positivity) (sub_nonneg.mpr hwD)
    dsimp [A, D] at *
    nlinarith only [h1, h2, h3]
  have hmon : D * F L w ≤ w * F L D := by
    have := mul_nonneg (sub_nonneg.mpr hwD) hinner
    dsimp [F]
    nlinarith only [this]
  have hendpoint : F L D ≤ 3 * B * D := by
    dsimp [F, A, D, L, B]
    unfold relayError at he
    nlinarith only [he]
  have hbad : 3 * B * D * w < 3 * B * D * w := by
    calc
      3 * B * D * w = D * (3 * B * w) := by ring
      _ < D * F b w := mul_lt_mul_of_pos_left hfailed hD
      _ ≤ D * F L w := mul_le_mul_of_nonneg_left hcompare hD.le
      _ ≤ w * F L D := hmon
      _ ≤ w * (3 * B * D) := mul_le_mul_of_nonneg_left hendpoint hw.le
      _ = _ := by ring
  exact (lt_irrefl _) hbad

theorem high_anchor_strict_relay (d p δ w b q : ℝ)
    (hd : 0 < d) (hd7 : d ≤ 7 / 40) (hp : 0 ≤ p)
    (hcredit : (1 : ℝ) / 2 ≤ p ∨ d ≤ p * (1 - p))
    (hδ : 0 ≤ δ) (hr : δ + w ≤ 1 - d)
    (hden : 0 < δ + w) (hb : p + d ≤ b) (hq1 : 1 ≤ q)
    (hatt : q * (δ + w) = 3 * w - b - 3 * d)
    (hfail : 3 * (1 - 4 * d) < (2 * (1 - d) - b - w) * q) :
    ∀ z : ℝ, (3 : ℝ) / 4 <
      (1 - d) - δ * z - (1 - d - δ - w) * z * (1 - z) := by
  have hq3 : q < 3 := by
    by_contra hn
    have := mul_le_mul_of_nonneg_right (le_of_not_gt hn) hden.le
    linarith
  have hwD := (high_anchor_gap d p δ w b q hd hd7 hp hcredit hδ hb hq1 hq3 hatt hfail).le
  have hq : 0 < q := by linarith
  have hbupper : b ≤ 2 * (1 - d) - w := by
    by_contra hn
    have := mul_nonpos_of_nonpos_of_nonneg (show 2 * (1 - d) - b - w ≤ 0 by linarith) hq.le
    linarith
  have he : relayError (1 - d) (3 * d) b w ≤ 0 := by
    by_cases hLD : 3 * d ≤ p + d
    · exact relayError_nonpos_of_baseline _ _ _ _ (by positivity) hwD
        (by linarith) (hLD.trans hb) hbupper
    · have hc : d ≤ p * (1 - p) := by
        rcases hcredit with h | h
        · linarith
        · exact h
      have hL := high_anchor_low_baseline_error d p hd.le hd7 hp (by linarith) hc
      have hslope : 3 * d - 2 * (p + d) ≤ 0 := by nlinarith [sq_nonneg p]
      have hmove := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hwD) hslope
      have hlow : relayError (1 - d) (3 * d) (p + d) w ≤ 0 := by
        unfold relayError at *
        nlinarith only [hL, hmove]
      have hhigh := relayError_upper_endpoint (1 - d) (3 * d) w
        (by positivity) hwD (by linarith)
      have hh := quadratic_nonpositive_between (-(2 * (1 - d) + 2 * w - 3 * d))
        (3 * d * ((1 - d) + w)) (p + d) (2 * (1 - d) - w) b hb hbupper
        (by unfold relayError at hlow; nlinarith only [hlow])
        (by unfold relayError at hhigh; nlinarith only [hhigh])
      unfold relayError
      nlinarith only [hh]
  have hm := credit_to_strict_determinant (1 - d) (3 * d) δ w b q hden hatt
    (by linarith) he
  have hdisc : (δ + (1 - d - δ - w)) ^ 2 <
      (4 * (1 - d) - 3) * (1 - d - δ - w) := by nlinarith only [hm]
  have hr0 : 0 < 1 - d - δ - w := by
    have hrnonneg : 0 ≤ 1 - d - δ - w := by linarith
    nlinarith [sq_nonneg (δ + (1 - d - δ - w))]
  exact strict_edge_of_discriminant (1 - d) δ (1 - d - δ - w) hr0 hdisc

end ConsistentSubmodular
