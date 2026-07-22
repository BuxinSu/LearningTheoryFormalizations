import HighDimensionalProbability.Appendix.Infra.PoincareCap

/-!
# Chordal expansion geometry for spherical caps

This file gives an explicit point on a cap boundary and a quantitative
distance estimate.  The estimate is arranged so that, after the Poincaré
rescaling, a cap threshold shifted by any `s < ε` lies in the chordal
`ε / √d`-expansion of the original cap for all sufficiently large `d`.
-/

open MeasureTheory ProbabilityTheory Set Metric InnerProductSpace Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology

namespace HDP.Appendix

/-- Move `x` to the boundary of the cap with normal `u` and threshold `b`,
while retaining the component of `x` orthogonal to `u`. -/
noncomputable def capBoundaryPoint {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (u x : E) (b : ℝ) : E :=
  let r := inner ℝ u x
  let w := x - r • u
  b • u + (Real.sqrt (1 - b ^ 2) / Real.sqrt (1 - r ^ 2)) • w

lemma inner_capBoundaryPoint {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (u x : E) (b : ℝ)
    (hu : ‖u‖ = 1) :
    inner ℝ u (capBoundaryPoint u x b) = b := by
  rw [capBoundaryPoint]
  simp only [inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq,
    hu, one_pow, mul_one, inner_sub_right]
  ring

lemma inner_capBoundaryOrth {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (u x : E) (hu : ‖u‖ = 1) :
    inner ℝ u (x - inner ℝ u x • u) = 0 := by
  simp [inner_sub_right, inner_smul_right, hu]

lemma norm_sq_capBoundaryOrth {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (u x : E) (hu : ‖u‖ = 1) (hx : ‖x‖ = 1) :
    ‖x - inner ℝ u x • u‖ ^ 2 = 1 - (inner ℝ u x) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
    real_inner_self_eq_norm_sq, hu, hx, one_pow, mul_one]
  rw [real_inner_comm u x]
  ring

lemma norm_capBoundaryPoint {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (u x : E) (b : ℝ)
    (hu : ‖u‖ = 1) (hx : ‖x‖ = 1)
    (hb : |b| < 1) (hr : |inner ℝ u x| < 1) :
    ‖capBoundaryPoint u x b‖ = 1 := by
  let r := inner ℝ u x
  let w := x - r • u
  have hworth : inner ℝ u w = 0 := by
    dsimp [w, r]
    exact inner_capBoundaryOrth u x hu
  have hworth' : inner ℝ w u = 0 := by
    rw [real_inner_comm, hworth]
  have hwnorm : ‖w‖ ^ 2 = 1 - r ^ 2 := by
    dsimp [w, r]
    exact norm_sq_capBoundaryOrth u x hu hx
  have hbpos : 0 < 1 - b ^ 2 := by
    have hsq : b ^ 2 < 1 := (sq_lt_one_iff_abs_lt_one b).2 hb
    linarith
  have hrpos : 0 < 1 - r ^ 2 := by
    have hsq : r ^ 2 < 1 := by
      dsimp [r]
      exact (sq_lt_one_iff_abs_lt_one _).2 hr
    linarith
  have hsqrtr : Real.sqrt (1 - r ^ 2) ≠ 0 :=
    (Real.sqrt_pos.2 hrpos).ne'
  rw [← sq_eq_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)]
  rw [one_pow, ← real_inner_self_eq_norm_sq]
  change inner ℝ
    (b • u + (Real.sqrt (1 - b ^ 2) / Real.sqrt (1 - r ^ 2)) • w)
    (b • u + (Real.sqrt (1 - b ^ 2) / Real.sqrt (1 - r ^ 2)) • w) = 1
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    starRingEnd_apply, star_id_of_comm, real_inner_self_eq_norm_sq, hu, one_pow,
    hworth, hworth', mul_zero, add_zero, zero_add, hwnorm]
  field_simp [hsqrtr]
  nlinarith [Real.sq_sqrt hbpos.le, Real.sq_sqrt hrpos.le]

lemma dist_capBoundaryPoint_sq {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (u x : E) (b : ℝ)
    (hu : ‖u‖ = 1) (hx : ‖x‖ = 1)
    (hr : |inner ℝ u x| < 1) :
    dist x (capBoundaryPoint u x b) ^ 2 =
      (inner ℝ u x - b) ^ 2 +
        (Real.sqrt (1 - (inner ℝ u x) ^ 2) -
          Real.sqrt (1 - b ^ 2)) ^ 2 := by
  let r := inner ℝ u x
  let w := x - r • u
  let qr := Real.sqrt (1 - r ^ 2)
  let qb := Real.sqrt (1 - b ^ 2)
  have hworth : inner ℝ u w = 0 := by
    dsimp [w, r]
    exact inner_capBoundaryOrth u x hu
  have hworth' : inner ℝ w u = 0 := by
    rw [real_inner_comm, hworth]
  have hwnorm : ‖w‖ ^ 2 = 1 - r ^ 2 := by
    dsimp [w, r]
    exact norm_sq_capBoundaryOrth u x hu hx
  have hrpos : 0 < 1 - r ^ 2 := by
    have hsq : r ^ 2 < 1 := by
      dsimp [r]
      exact (sq_lt_one_iff_abs_lt_one _).2 hr
    linarith
  have hqr : qr ≠ 0 := by
    dsimp [qr]
    exact (Real.sqrt_pos.2 hrpos).ne'
  rw [dist_eq_norm, ← real_inner_self_eq_norm_sq]
  have hdecomp : x - capBoundaryPoint u x b =
      (r - b) • u + (1 - qb / qr) • w := by
    dsimp [capBoundaryPoint, r, w, qb, qr]
    module
  rw [hdecomp]
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    starRingEnd_apply, star_id_of_comm, real_inner_self_eq_norm_sq, hu, one_pow,
    hworth, hworth', mul_zero, add_zero, zero_add, hwnorm]
  change (r - b) * ((r - b) * 1) +
      (1 - qb / qr) * ((1 - qb / qr) * (1 - r ^ 2)) =
    (r - b) ^ 2 + (qr - qb) ^ 2
  simp only [mul_one]
  have hqrsq : qr ^ 2 = 1 - r ^ 2 := by
    dsimp [qr]
    exact Real.sq_sqrt hrpos.le
  field_simp [hqr]
  nlinarith

lemma sqrt_one_sub_sq_diff_sq_le {b r : ℝ}
    (hb : |b| ≤ 1 / 2) (hr : |r| ≤ 1 / 2) :
    (Real.sqrt (1 - r ^ 2) - Real.sqrt (1 - b ^ 2)) ^ 2 ≤
      (r - b) ^ 2 * (r + b) ^ 2 := by
  let qr := Real.sqrt (1 - r ^ 2)
  let qb := Real.sqrt (1 - b ^ 2)
  have hbSq : b ^ 2 ≤ (1 / 2 : ℝ) ^ 2 :=
    (sq_le_sq).2 (by simpa using hb)
  have hrSq : r ^ 2 ≤ (1 / 2 : ℝ) ^ 2 :=
    (sq_le_sq).2 (by simpa using hr)
  have hbbase : 0 ≤ 1 - b ^ 2 := by nlinarith
  have hrbase : 0 ≤ 1 - r ^ 2 := by nlinarith
  have hqb : 1 / 2 ≤ qb := by
    dsimp [qb]
    rw [Real.le_sqrt (by norm_num) hbbase]
    nlinarith
  have hqr : 1 / 2 ≤ qr := by
    dsimp [qr]
    rw [Real.le_sqrt (by norm_num) hrbase]
    nlinarith
  have hsum : 1 ≤ qr + qb := by linarith
  have hmul : |qr - qb| ≤ |qr - qb| * (qr + qb) := by
    nlinarith [abs_nonneg (qr - qb)]
  have hid : (qr - qb) * (qr + qb) = b ^ 2 - r ^ 2 := by
    have hqrsq : qr ^ 2 = 1 - r ^ 2 := by
      dsimp [qr]
      exact Real.sq_sqrt hrbase
    have hqbsq : qb ^ 2 = 1 - b ^ 2 := by
      dsimp [qb]
      exact Real.sq_sqrt hbbase
    nlinarith
  have habs : |qr - qb| * (qr + qb) = |b ^ 2 - r ^ 2| := by
    rw [← abs_of_nonneg (by linarith : 0 ≤ qr + qb), ← abs_mul, hid]
  have hfactor : |b ^ 2 - r ^ 2| = |r - b| * |r + b| := by
    rw [show b ^ 2 - r ^ 2 = -(r - b) * (r + b) by ring,
      abs_mul, abs_neg]
  have hle : |qr - qb| ≤ |r - b| * |r + b| := by
    calc
      |qr - qb| ≤ |qr - qb| * (qr + qb) := hmul
      _ = |b ^ 2 - r ^ 2| := habs
      _ = |r - b| * |r + b| := hfactor
  have hle' : |qr - qb| ≤ |(r - b) * (r + b)| := by
    simpa [abs_mul] using hle
  have hsquare := (sq_le_sq).2 hle'
  simpa [qr, qb, mul_pow] using hsquare

/-- A quantitative finite-dimensional cap-expansion inclusion.  The
parameter `B` bounds both cap thresholds; when `B` is small, the chordal
distance is asymptotic to the threshold shift. -/
lemma sphericalCap_shift_subset_closedExpansion
    {d : ℕ} (u : EuclideanSpace ℝ (Fin d)) (hu : ‖u‖ = 1)
    {b h δ B : ℝ} (hB0 : 0 ≤ B) (hB : B ≤ 1 / 2)
    (hb : |b| ≤ B) (hbh : |b + h| ≤ B) (hh : 0 ≤ h)
    (hdist : h ^ 2 * (1 + (2 * B) ^ 2) ≤ δ ^ 2)
    (hδ : 0 ≤ δ) :
    HDP.Chapter5.sphericalCap u (b + h) ⊆
      closedExpansion δ (HDP.Chapter5.sphericalCap u b) := by
  intro x hx
  let r := inner ℝ u (x : EuclideanSpace ℝ (Fin d))
  have hxnorm : ‖(x : EuclideanSpace ℝ (Fin d))‖ = 1 := by
    simpa [mem_sphere_zero_iff_norm] using x.property
  change r ≤ b + h at hx
  by_cases hrb : r ≤ b
  · exact ⟨x, hrb, by simpa using hδ⟩
  · have hbr : b < r := lt_of_not_ge hrb
    have hb_bounds := abs_le.mp hb
    have hbhB := abs_le.mp hbh
    have hr_lower : -B ≤ r := hb_bounds.1.trans (le_of_lt hbr)
    have hr_upper : r ≤ B := hx.trans hbhB.2
    have hrB : |r| ≤ B := abs_le.mpr ⟨hr_lower, hr_upper⟩
    have hbhalf : |b| < 1 :=
      lt_of_le_of_lt (hb.trans hB) (by norm_num)
    have hrhalf : |r| < 1 :=
      lt_of_le_of_lt (hrB.trans hB) (by norm_num)
    let yv := capBoundaryPoint u (x : EuclideanSpace ℝ (Fin d)) b
    have hynorm : ‖yv‖ = 1 :=
      norm_capBoundaryPoint u (x : EuclideanSpace ℝ (Fin d)) b
        hu hxnorm hbhalf hrhalf
    let y : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 :=
      ⟨yv, by simpa [mem_sphere_zero_iff_norm] using hynorm⟩
    refine ⟨y, ?_, ?_⟩
    · change inner ℝ u yv ≤ b
      rw [inner_capBoundaryPoint u (x : EuclideanSpace ℝ (Fin d)) b hu]
    · have hsqdist := dist_capBoundaryPoint_sq
        u (x : EuclideanSpace ℝ (Fin d)) b hu hxnorm hrhalf
      have hsqrtBound := sqrt_one_sub_sq_diff_sq_le
        (hb.trans hB) (hrB.trans hB)
      have hrb0 : 0 ≤ r - b := sub_nonneg.mpr hbr.le
      have hrbh' : r - b ≤ h := by linarith
      have hsqrb : (r - b) ^ 2 ≤ h ^ 2 :=
        (sq_le_sq₀ hrb0 hh).2 hrbh'
      have hrbSum : |r + b| ≤ 2 * B := by
        calc
          |r + b| ≤ |r| + |b| := abs_add_le _ _
          _ ≤ B + B := add_le_add hrB hb
          _ = 2 * B := by ring
      have htwoB : 0 ≤ 2 * B := mul_nonneg (by norm_num) hB0
      have hsqsum : (r + b) ^ 2 ≤ (2 * B) ^ 2 := by
        rw [sq_le_sq]
        simpa [abs_of_nonneg htwoB] using hrbSum
      have hfac :
          (r - b) ^ 2 * (1 + (r + b) ^ 2) ≤
            h ^ 2 * (1 + (2 * B) ^ 2) := by
        gcongr
      have hdistSq : dist (x : EuclideanSpace ℝ (Fin d)) yv ^ 2 ≤ δ ^ 2 := by
        rw [hsqdist]
        calc
          (r - b) ^ 2 +
              (Real.sqrt (1 - r ^ 2) - Real.sqrt (1 - b ^ 2)) ^ 2
              ≤ (r - b) ^ 2 + (r - b) ^ 2 * (r + b) ^ 2 := by
                simpa [add_comm] using
                  add_le_add_left hsqrtBound ((r - b) ^ 2)
          _ = (r - b) ^ 2 * (1 + (r + b) ^ 2) := by ring
          _ ≤ h ^ 2 * (1 + (2 * B) ^ 2) := hfac
          _ ≤ δ ^ 2 := hdist
      change dist (x : EuclideanSpace ℝ (Fin d)) yv ≤ δ
      exact (sq_le_sq₀ dist_nonneg hδ).1 hdistSq

/-- Uniform asymptotic form of the cap-expansion inclusion.  If the scaled
cap thresholds `t k` converge and `0 ≤ s < ε`, then the cap shifted by `s`
is contained in the chordal `ε / √d`-expansion for all sufficiently large
ambient dimensions. -/
lemma poincare_sphericalCap_shift_subset_expansion_eventually
    (n : ℕ) {t : ℕ → ℝ} {a s ε : ℝ}
    (ht : Tendsto t atTop (𝓝 a)) (hs : 0 ≤ s) (hsε : s < ε) :
    ∀ᶠ k : ℕ in atTop,
      ∀ u : EuclideanSpace ℝ (Fin (n + (k + 2))), ‖u‖ = 1 →
        HDP.Chapter5.sphericalCap u
            ((t k + s) / Real.sqrt (n + (k + 2) : ℝ)) ⊆
          closedExpansion (ε / Real.sqrt (n + (k + 2) : ℝ))
            (HDP.Chapter5.sphericalCap u
              (t k / Real.sqrt (n + (k + 2) : ℝ))) := by
  let M : ℝ := |a| + |s| + 1
  have hMpos : 0 < M := by
    dsimp [M]
    positivity
  have hM0 : 0 ≤ M := hMpos.le
  have hD : Tendsto (fun k : ℕ => (n + (k + 2) : ℝ)) atTop atTop := by
    have hNat : Tendsto (fun k : ℕ => n + (k + 2)) atTop atTop := by
      convert tendsto_add_atTop_nat (n + 2) using 1
      ext k
      omega
    have hCast :=
      (tendsto_natCast_atTop_atTop :
        Tendsto (fun m : ℕ => (m : ℝ)) atTop atTop).comp hNat
    convert hCast using 1
    ext k
    simp only [Function.comp_apply, Nat.cast_add, Nat.cast_ofNat]
  have hsqrt :
      Tendsto (fun k : ℕ => Real.sqrt (n + (k + 2) : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hD
  have hBlim : Tendsto
      (fun k : ℕ => M / Real.sqrt (n + (k + 2) : ℝ)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using hsqrt.inv_tendsto_atTop.const_mul M
  have hsmallB : ∀ᶠ k : ℕ in atTop,
      M / Real.sqrt (n + (k + 2) : ℝ) ≤ 1 / 2 :=
    hBlim.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 2)
  have hprofile : Tendsto
      (fun k : ℕ => s ^ 2 *
        (1 + (2 * (M / Real.sqrt (n + (k + 2) : ℝ))) ^ 2))
      atTop (𝓝 (s ^ 2)) := by
    convert tendsto_const_nhds.mul
      (tendsto_const_nhds.add ((tendsto_const_nhds.mul hBlim).pow 2))
      using 1 <;> ring
  have hεpos : 0 < ε := lt_of_le_of_lt hs hsε
  have hsquare : s ^ 2 < ε ^ 2 := (sq_lt_sq₀ hs hεpos.le).2 hsε
  have hdistEv : ∀ᶠ k : ℕ in atTop,
      s ^ 2 * (1 + (2 * (M / Real.sqrt (n + (k + 2) : ℝ))) ^ 2) ≤
        ε ^ 2 :=
    (hprofile.eventually_lt_const hsquare).mono fun _ h => h.le
  have htnear : ∀ᶠ k : ℕ in atTop, |t k - a| < 1 := by
    have h := ht.eventually (Metric.ball_mem_nhds a zero_lt_one)
    simpa [Real.dist_eq] using h
  filter_upwards [hsmallB, hdistEv, htnear] with k hkB hkdist hkt
  intro u hu
  have hdim : 0 < n + (k + 2) := by omega
  have hdimR : 0 < (n + (k + 2) : ℝ) := by exact_mod_cast hdim
  have hsqrtPos : 0 < Real.sqrt (n + (k + 2) : ℝ) :=
    Real.sqrt_pos.2 hdimR
  have htk : |t k| ≤ |a| + 1 := by
    calc
      |t k| = |(t k - a) + a| := by ring_nf
      _ ≤ |t k - a| + |a| := abs_add_le _ _
      _ ≤ 1 + |a| := by linarith
      _ = |a| + 1 := by ring
  have htks : |t k + s| ≤ M := by
    calc
      |t k + s| ≤ |t k| + |s| := abs_add_le _ _
      _ ≤ (|a| + 1) + |s| := by linarith
      _ = M := by simp [M]; ring
  have htkM : |t k| ≤ M := by
    dsimp [M]
    nlinarith [abs_nonneg s]
  have hsub :
      HDP.Chapter5.sphericalCap u
          (t k / Real.sqrt (n + (k + 2) : ℝ) +
            s / Real.sqrt (n + (k + 2) : ℝ)) ⊆
        closedExpansion (ε / Real.sqrt (n + (k + 2) : ℝ))
          (HDP.Chapter5.sphericalCap u
            (t k / Real.sqrt (n + (k + 2) : ℝ))) := by
    apply sphericalCap_shift_subset_closedExpansion u hu
      (B := M / Real.sqrt (n + (k + 2) : ℝ))
    · exact div_nonneg hM0 hsqrtPos.le
    · exact hkB
    · rw [abs_div, abs_of_pos hsqrtPos]
      exact div_le_div_of_nonneg_right htkM hsqrtPos.le
    · rw [← add_div, abs_div, abs_of_pos hsqrtPos]
      exact div_le_div_of_nonneg_right htks hsqrtPos.le
    · exact div_nonneg hs hsqrtPos.le
    · rw [div_pow, div_pow]
      calc
        s ^ 2 / Real.sqrt (n + (k + 2) : ℝ) ^ 2 *
              (1 + (2 * (M / Real.sqrt (n + (k + 2) : ℝ))) ^ 2) =
            (s ^ 2 *
              (1 + (2 * (M / Real.sqrt (n + (k + 2) : ℝ))) ^ 2)) /
                Real.sqrt (n + (k + 2) : ℝ) ^ 2 := by ring
        _ ≤ ε ^ 2 / Real.sqrt (n + (k + 2) : ℝ) ^ 2 :=
          (div_le_div_iff_of_pos_right (sq_pos_of_pos hsqrtPos)).2 hkdist
    · exact div_nonneg hεpos.le hsqrtPos.le
  simpa [add_div] using hsub

end HDP.Appendix
