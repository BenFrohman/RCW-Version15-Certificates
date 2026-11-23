/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

import Mathlib

/-!
# RCW.R2TwistFibers

Machine-checked certificate that residual R2 has no solutions
on any twist fiber with 1 ≤ |d| ≤ (r - 3)/2.
-/

namespace RCW.R2TwistFibers

theorem R2_positive_fiber_no_square
    (r d Y : ℤ) (hr : 5 ≤ r) (hd_pos : 1 ≤ d) (hd_ub : 2 * d ≤ r - 3)
    (h_eq : Y ^ 2 = r ^ 6 + 2 * r ^ 5 + r ^ 4 + r ^ 3 + (2 * r ^ 2 + r + 1) * d) :
    False := by
  have hr_pos : 0 < r := by linarith
  have hQ : 0 < 2 * r ^ 2 + r + 1 := by nlinarith
  have h_low : (r ^ 3 + r ^ 2) ^ 2 < Y ^ 2 := by
    have hdiff : Y ^ 2 - (r ^ 3 + r ^ 2) ^ 2 =
        r ^ 3 + (2 * r ^ 2 + r + 1) * d := by
      rw [h_eq]; ring
    have h1 : 0 < r ^ 3 := pow_pos hr_pos 3
    have h2 : 0 < (2 * r ^ 2 + r + 1) * d := mul_pos hQ (by linarith : 0 < d)
    linarith
  have h_high : Y ^ 2 < (r ^ 3 + r ^ 2 + 1) ^ 2 := by
    have hmul : (2 * r ^ 2 + r + 1) * (2 * d) ≤
        (2 * r ^ 2 + r + 1) * (r - 3) :=
      mul_le_mul_of_nonneg_left hd_ub hQ.le
    have hpoly : (2 * r ^ 2 + r + 1) * (r - 3) =
        2 * r ^ 3 - 5 * r ^ 2 - 2 * r - 3 := by ring
    have htwice : 2 * ((r ^ 3 + r ^ 2 + 1) ^ 2 - Y ^ 2) =
        2 * (r ^ 3 + 2 * r ^ 2 + 1) - (2 * r ^ 2 + r + 1) * (2 * d) := by
      rw [h_eq]; ring
    have hident : 2 * (r ^ 3 + 2 * r ^ 2 + 1) - (2 * r ^ 3 - 5 * r ^ 2 - 2 * r - 3) =
        9 * r ^ 2 + 2 * r + 5 := by ring
    have h9 : 0 < 9 * r ^ 2 + 2 * r + 5 := by nlinarith
    have hge : 9 * r ^ 2 + 2 * r + 5 ≤
        2 * ((r ^ 3 + r ^ 2 + 1) ^ 2 - Y ^ 2) := by
      linarith [htwice, hmul, hpoly, hident]
    linarith
  have h1 : r ^ 3 + r ^ 2 < |Y| := by
    have habs : |r ^ 3 + r ^ 2| < |Y| := (sq_lt_sq).mp h_low
    have hA : 0 ≤ r ^ 3 + r ^ 2 := by nlinarith
    simpa [abs_of_nonneg hA] using habs
  have h2 : |Y| < r ^ 3 + r ^ 2 + 1 := by
    have habs : |Y| < |r ^ 3 + r ^ 2 + 1| := (sq_lt_sq).mp h_high
    have hA1 : 0 ≤ r ^ 3 + r ^ 2 + 1 := by nlinarith
    simpa [abs_of_nonneg hA1] using habs
  omega

theorem R2_negative_fiber_no_square
    (r d Y : ℤ) (hr : 5 ≤ r) (hd_neg : d ≤ -1) (hd_lb : -(r - 3) ≤ 2 * d)
    (h_eq : Y ^ 2 = r ^ 6 + 2 * r ^ 5 + r ^ 4 + r ^ 3 + (2 * r ^ 2 + r + 1) * d) :
    False := by
  have hr_pos : 0 < r := by linarith
  have hQ : 0 < 2 * r ^ 2 + r + 1 := by nlinarith
  have h_low : (r ^ 3 + r ^ 2) ^ 2 < Y ^ 2 := by
    have hbd : -(2 * d) ≤ r - 3 := by linarith
    have hmul : (2 * r ^ 2 + r + 1) * (-(2 * d)) ≤
        (2 * r ^ 2 + r + 1) * (r - 3) :=
      mul_le_mul_of_nonneg_left hbd hQ.le
    have hpoly : (2 * r ^ 2 + r + 1) * (r - 3) =
        2 * r ^ 3 - 5 * r ^ 2 - 2 * r - 3 := by ring
    have htwice : 2 * (Y ^ 2 - (r ^ 3 + r ^ 2) ^ 2) =
        2 * r ^ 3 - (2 * r ^ 2 + r + 1) * (-(2 * d)) := by
      rw [h_eq]; ring
    have hident : 2 * r ^ 3 - (2 * r ^ 3 - 5 * r ^ 2 - 2 * r - 3) =
        5 * r ^ 2 + 2 * r + 3 := by ring
    have h5 : 0 < 5 * r ^ 2 + 2 * r + 3 := by nlinarith
    have hge : 5 * r ^ 2 + 2 * r + 3 ≤
        2 * (Y ^ 2 - (r ^ 3 + r ^ 2) ^ 2) := by
      linarith [htwice, hmul, hpoly, hident]
    linarith
  have h_high : Y ^ 2 < (r ^ 3 + r ^ 2 + 1) ^ 2 := by
    have hgap : (r ^ 3 + r ^ 2 + 1) ^ 2 - Y ^ 2 =
        r ^ 3 + 2 * r ^ 2 + 1 - (2 * r ^ 2 + r + 1) * d := by
      rw [h_eq]; ring
    have hQd : (2 * r ^ 2 + r + 1) * d ≤
        (2 * r ^ 2 + r + 1) * (-1) :=
      mul_le_mul_of_nonneg_left hd_neg hQ.le
    have hneg : (2 * r ^ 2 + r + 1) * (-1) = -(2 * r ^ 2 + r + 1) := by ring
    have hpos : 0 < r ^ 3 + 2 * r ^ 2 + 1 := by positivity
    linarith
  have h1 : r ^ 3 + r ^ 2 < |Y| := by
    have habs : |r ^ 3 + r ^ 2| < |Y| := (sq_lt_sq).mp h_low
    have hA : 0 ≤ r ^ 3 + r ^ 2 := by nlinarith
    simpa [abs_of_nonneg hA] using habs
  have h2 : |Y| < r ^ 3 + r ^ 2 + 1 := by
    have habs : |Y| < |r ^ 3 + r ^ 2 + 1| := (sq_lt_sq).mp h_high
    have hA1 : 0 ≤ r ^ 3 + r ^ 2 + 1 := by nlinarith
    simpa [abs_of_nonneg hA1] using habs
  omega

end RCW.R2TwistFibers
