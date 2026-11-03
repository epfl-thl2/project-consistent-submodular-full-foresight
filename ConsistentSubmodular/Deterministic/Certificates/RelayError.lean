module

public import ConsistentSubmodular.Deterministic.Certificates.RelayScalar

@[expose] public section

/-! Credit-to-edge error bounds for forward relays. -/

namespace ConsistentSubmodular

/-- A convex monic quadratic is nonpositive between nonpositive endpoints. -/
theorem quadratic_nonpositive_between (c d l u x : ℝ)
    (hlx : l ≤ x) (hxu : x ≤ u)
    (hl : l ^ 2 + c * l + d ≤ 0) (hu : u ^ 2 + c * u + d ≤ 0) :
    x ^ 2 + c * x + d ≤ 0 := by
  by_cases h : x + l + c ≤ 0
  · nlinarith [mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hlx) h]
  · have hp : 0 ≤ x + u + c := by linarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hxu) hp]

def relayError (A D b w : ℝ) : ℝ :=
  b ^ 2 - b * (2 * A + 2 * w - D) + D * (A + w)

theorem relayError_upper_endpoint (A D w : ℝ)
    (hD : 0 ≤ D) (hDw : D ≤ w) (hwA : w ≤ A) :
    relayError A D (2 * A - w) w ≤ 0 := by
  have hw : 0 ≤ w := hD.trans hDw
  have hA : 0 ≤ A := hw.trans hwA
  have h1 := mul_nonneg hw (sub_nonneg.mpr hwA)
  have h2 := mul_nonneg hA (sub_nonneg.mpr hDw)
  unfold relayError
  nlinarith

theorem relayError_nonpos_of_baseline (A D b w : ℝ)
    (hD : 0 ≤ D) (hDw : D ≤ w) (hwA : w ≤ A)
    (hDb : D ≤ b) (hb : b ≤ 2 * A - w) : relayError A D b w ≤ 0 := by
  have hlow : relayError A D D w ≤ 0 := by
    have := mul_nonpos_of_nonneg_of_nonpos hD (show 2 * D - A - w ≤ 0 by linarith)
    unfold relayError
    nlinarith
  have hhigh := relayError_upper_endpoint A D w hD hDw hwA
  have h := quadratic_nonpositive_between (-(2 * A + 2 * w - D)) (D * (A + w))
    D (2 * A - w) b hDb hb
    (by unfold relayError at hlow; nlinarith only [hlow])
    (by unfold relayError at hhigh; nlinarith only [hhigh])
  unfold relayError
  nlinarith only [h]

/-- The explicit Bernstein certificate used by the large-parameter relay. -/
theorem high_relay_cubic_nonpositive (p : ℝ) (hp : 0 ≤ p) (hp2 : p ≤ 1 / 2) :
    17 * p ^ 3 - 41 * p ^ 2 + 20 * p - 3 ≤ 0 := by
  by_cases hquarter : p ≤ 1 / 4
  · have ht : 0 ≤ 4 * p := by positivity
    have hs : 0 ≤ 1 - 4 * p := by linarith
    have hid : 17 * p ^ 3 - 41 * p ^ 2 + 20 * p - 3 =
        -(3 * (1 - 4 * p) ^ 3 + 4 * (4 * p) * (1 - 4 * p) ^ 2 +
          (25 / 16 : ℝ) * (4 * p) ^ 2 * (1 - 4 * p) +
          (19 / 64 : ℝ) * (4 * p) ^ 3) := by ring
    rw [hid]
    have : 0 ≤ 3 * (1 - 4 * p) ^ 3 + 4 * (4 * p) * (1 - 4 * p) ^ 2 +
        (25 / 16 : ℝ) * (4 * p) ^ 2 * (1 - 4 * p) +
        (19 / 64 : ℝ) * (4 * p) ^ 3 := by positivity
    linarith
  · have ht : 0 ≤ 4 * p - 1 := by linarith
    have hs : 0 ≤ 2 - 4 * p := by linarith
    have hid : 17 * p ^ 3 - 41 * p ^ 2 + 20 * p - 3 =
        -((19 / 64 : ℝ) * (2 - 4 * p) ^ 3 +
          (7 / 32 : ℝ) * (4 * p - 1) * (2 - 4 * p) ^ 2 +
          (21 / 16 : ℝ) * (4 * p - 1) ^ 2 * (2 - 4 * p) +
          (9 / 8 : ℝ) * (4 * p - 1) ^ 3) := by ring
    rw [hid]
    have : 0 ≤ (19 / 64 : ℝ) * (2 - 4 * p) ^ 3 +
        (7 / 32 : ℝ) * (4 * p - 1) * (2 - 4 * p) ^ 2 +
        (21 / 16 : ℝ) * (4 * p - 1) ^ 2 * (2 - 4 * p) +
        (9 / 8 : ℝ) * (4 * p - 1) ^ 3 := by positivity
    linarith

theorem relayError_low_baseline (d p w : ℝ)
    (hd : 0 ≤ d) (hp : 0 ≤ p) (hp2 : p ≤ 1 / 2)
    (hcredit : d ≤ p * (1 - p))
    (hw : 2 * ((p + d) + 3 * d) / 3 ≤ w) :
    relayError (1 - d) (3 * d) (p + d) w ≤ 0 := by
  have hpd : d ≤ p := by nlinarith [sq_nonneg p]
  have hslope : 3 * d - 2 * (p + d) ≤ 0 := by linarith
  have hmove := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hw) hslope
  have hcoef : 0 ≤ 7 * p + 3 + 17 * (p * (1 - p) + d) := by
    have hp1 : 0 ≤ 1 - p := by linarith
    positivity
  have hinc := mul_nonneg (sub_nonneg.mpr hcredit) hcoef
  have hcubic := mul_nonpos_of_nonneg_of_nonpos hp (high_relay_cubic_nonpositive p hp hp2)
  unfold relayError
  nlinarith only [hmove, hinc, hcubic]

/-- Strong credit makes the error term nonpositive throughout the
large-parameter source domain. -/
theorem relayError_high_parameter (d p b w : ℝ)
    (hd : 0 ≤ d) (hd4 : d < 1 / 4) (hp : 0 ≤ p)
    (hcredit : (1 : ℝ) / 2 ≤ p ∨ d ≤ p * (1 - p))
    (hDw : 3 * d ≤ w) (hwA : w ≤ 1 - d)
    (hbL : p + d ≤ b) (hb : b ≤ 2 * (1 - d) - w)
    (hw : 2 * ((p + d) + 3 * d) / 3 ≤ w) :
    relayError (1 - d) (3 * d) b w ≤ 0 := by
  by_cases hLD : 3 * d ≤ p + d
  · exact relayError_nonpos_of_baseline _ _ _ _ (by positivity) hDw hwA
      (hLD.trans hbL) hb
  · have hp2 : p ≤ 1 / 2 := by linarith
    have hc : d ≤ p * (1 - p) := by
      rcases hcredit with h | h
      · linarith
      · exact h
    have hlow := relayError_low_baseline d p w hd hp hp2 hc hw
    have hhigh := relayError_upper_endpoint (1 - d) (3 * d) w
      (by positivity) hDw hwA
    have h := quadratic_nonpositive_between (-(2 * (1 - d) + 2 * w - 3 * d))
      (3 * d * ((1 - d) + w)) (p + d) (2 * (1 - d) - w) b hbL hb
      (by unfold relayError at hlow; nlinarith only [hlow])
      (by unfold relayError at hhigh; nlinarith only [hhigh])
    unfold relayError
    nlinarith only [h]

theorem credit_to_strict_determinant (A D δ w b q : ℝ)
    (hden : 0 < δ + w)
    (hatt : q * (δ + w) = 3 * w - b - D)
    (hfail : 3 * (A - D) < (2 * A - b - w) * q)
    (herror : relayError A D b w ≤ 0) :
    0 < (A - w) * (w - D) - (A - D) * δ := by
  have hid :
      (δ + w) * ((2 * A - b - w) * q - 3 * (A - D)) =
        3 * ((A - w) * (w - D) - (A - D) * δ) + relayError A D b w := by
    calc
      _ = (q * (δ + w)) * (2 * A - b - w) - 3 * (A - D) * (δ + w) := by ring
      _ = _ := by rw [hatt]; unfold relayError; ring
  have := mul_pos hden (sub_pos.mpr hfail)
  linarith

/-- Failed credit at a parameter at least three halves yields a strictly safe
full forward edge, retaining the original initial target. -/
theorem high_parameter_strict_relay (d p δ w b q : ℝ)
    (hd : 0 ≤ d) (hd4 : d < 1 / 4) (hp : 0 ≤ p)
    (hcredit : (1 : ℝ) / 2 ≤ p ∨ d ≤ p * (1 - p))
    (hδ : 0 ≤ δ) (hw0 : 0 ≤ w) (hr : δ + w ≤ 1 - d)
    (hden : 0 < δ + w) (hb : p + d ≤ b)
    (hq : (3 : ℝ) / 2 ≤ q)
    (hatt : q * (δ + w) = 3 * w - b - 3 * d)
    (hfail : 3 * (1 - 4 * d) < (2 * (1 - d) - b - w) * q) :
    ∀ z : ℝ, (3 : ℝ) / 4 <
      (1 - d) - δ * z - (1 - d - δ - w) * z * (1 - z) := by
  have hq0 : 0 < q := by linarith
  have hbudget : 2 * d ≤ p + d := by
    rcases hcredit with h | h
    · linarith
    · nlinarith [sq_nonneg p]
  have hwbound : 2 * ((p + d) + 3 * d) / 3 ≤ w := by
    have h1 := mul_nonneg (show 0 ≤ q - 3 / 2 by linarith) hw0
    have h2 := mul_nonneg hq0.le hδ
    nlinarith
  have hDw : 3 * d ≤ w := by linarith
  have hbupper : b ≤ 2 * (1 - d) - w := by
    by_contra hn
    have hx : 2 * (1 - d) - b - w ≤ 0 := by linarith
    have := mul_nonpos_of_nonpos_of_nonneg hx hq0.le
    linarith
  have he := relayError_high_parameter d p b w hd hd4 hp hcredit hDw
    (by linarith) hb hbupper hwbound
  have hm := credit_to_strict_determinant (1 - d) (3 * d) δ w b q hden hatt
    (by linarith) he
  have hdisc : (δ + (1 - d - δ - w)) ^ 2 <
      (4 * (1 - d) - 3) * (1 - d - δ - w) := by nlinarith only [hm]
  have hr0 : 0 < 1 - d - δ - w := by
    have hrnonneg : 0 ≤ 1 - d - δ - w := by linarith
    nlinarith [sq_nonneg (δ + (1 - d - δ - w))]
  exact strict_edge_of_discriminant (1 - d) δ (1 - d - δ - w) hr0 hdisc

end ConsistentSubmodular
