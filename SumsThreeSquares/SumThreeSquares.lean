import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Data.Int.Star
import Mathlib.Data.Real.StarOrdered
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.NumberTheory.SumTwoSquares

import SumsThreeSquares.Mathlib.MeasureTheory.Group.GeometryOfNumbers

/-!
# Legendre's three squares theorem

We prove that a natural number is a sum of three squares if and only if it is not of the form
`4 ^ a * (8 * k + 7)`, following Ankeny's proof via Davenport's method in the geometry of numbers.

## Main results

* `Nat.eq_sq_add_sq_add_sq_of_dvd`: a squarefree `m` is a sum of three squares as soon as there
  are integers `0 < c` and `b` with `m ∣ c + 1` and `c ∣ b ^ 2 + m`.
* `Nat.eq_sq_add_sq_add_sq_of_squarefree`: a squarefree `m` with `m % 8 ≠ 7` is a sum of three
  squares.
* `Nat.four_pow_mul_ne_sq_add_sq_add_sq`: a number `4 ^ a * (8 * k + 7)` is not a sum of three
  squares.
* `Nat.eq_sq_add_sq_add_sq_iff`: **Legendre's three squares theorem**.

## Implementation notes

The blueprint chooses a prime `q` with prescribed quadratic characters and an auxiliary `t` with
`2 q t ^ 2 ≡ -1 [ZMOD m]`. Choosing instead `q` in a suitable residue class modulo `4 m`, we can
take `t = 1`: writing `c = q` (or `c = 2 q` when `m % 8 = 3`) we get `m ∣ c + 1`, and both cases of
the blueprint become instances of `Nat.eq_sq_add_sq_add_sq_of_dvd`.

The proof is organised in four layers:
* Minkowski's theorem applied to an ellipsoid of volume `8 √2 π / 3` gives integers with
  `R ^ 2 + Q (x, y) = m`, where `Q = c x ^ 2 + 2 b x y + k y ^ 2` has discriminant `-4 m`.
* `Q (x, y)` is a sum of two squares: after removing `gcd x y`, a prime `p ≡ 3 [MOD 4]` dividing
  `Q` cannot divide `m` (by squarefreeness) and cannot avoid it (since `-m` and `m ≡ R ^ 2` would
  both be squares modulo `p`).
* Dirichlet's theorem supplies `c` and `b`: for `m % 4 = 1` take `q ≡ 2 m - 1 [MOD 4 m]`, and
  otherwise `m = d a + 1` with `d ∈ {1, 2}` and `q ≡ a [MOD 4 m]`.
* Finally, writing `n = 4 ^ a * s ^ 2 * r` with `r` squarefree reduces the general case to the
  squarefree one.

## References

* N. C. Ankeny, *Sums of three squares*, Proc. Amer. Math. Soc. 8 (1957), 316–319.
* H. Davenport, *The geometry of numbers*, Math. Gazette 31 (1947), 206–210.
-/

open MeasureTheory Metric Real

private lemma quadForm_pos {m : ℕ} {c b : ℤ} (hm : 0 < m) (hc : 0 < c) {v : Fin 3 → ℤ}
    (hv : v ≠ 0) :
    0 < c * (c * v 0 + b * v 1 + m * v 2) ^ 2 + (c * v 0 + b * v 1) ^ 2 + m * v 1 ^ 2 := by
  -- the form is positive definite: the summand of the last nonzero coordinate is positive
  rcases eq_or_ne (v 1) 0 with h1 | h1
  · rcases eq_or_ne (v 0) 0 with h0 | h0
    · have h2 : v 2 ≠ 0 := fun h2 ↦ hv (funext fun i ↦ by fin_cases i <;> assumption)
      simp only [h0, h1, mul_zero, zero_add]
      positivity
    · simp only [h1, mul_zero, add_zero]
      positivity
  · positivity

private lemma two_pow_three_lt_volume_preimage_ball {m : ℕ} {c b : ℤ} (hm : 0 < m) (hc : 0 < c) :
    2 ^ 3 < volume (Matrix.toLin' !![√c * c, √c * b, √c * m; c, b, 0; 0, √m, 0] ⁻¹'
      (WithLp.toLp 2 ⁻¹' ball 0 √(2 * m * c))) := by
  -- the linear map has determinant `m c √(m c)`, so the preimage has volume `8 √2 π / 3`
  have hc' : (0 : ℝ) < c := mod_cast hc
  have hdet : LinearMap.det (Matrix.toLin' !![√c * c, √c * b, √c * m; c, b, 0; 0, √m, 0]) =
      √c * m * c * √m := by simp [Matrix.det_fin_three]
  have hd : 0 < √c * m * c * √m := by positivity
  rw [Measure.addHaar_preimage_linearMap _ (hdet ▸ hd.ne'),
    (PiLp.volume_preserving_toLp _).measure_preimage measurableSet_ball.nullMeasurableSet,
    EuclideanSpace.volume_ball_fin_three, hdet, ← ENNReal.ofReal_pow (sqrt_nonneg _),
    ← ENNReal.ofReal_mul (pow_nonneg (sqrt_nonneg _) 3), ← ENNReal.ofReal_mul (abs_nonneg _),
    show (2 : ENNReal) ^ 3 = .ofReal 8 by norm_num, ENNReal.ofReal_lt_ofReal_iff (by positivity),
    abs_of_pos (inv_pos.2 hd), pow_succ, sq_sqrt (by positivity), sqrt_mul' _ hc'.le,
    sqrt_mul' _ m.cast_nonneg]
  field_simp
  linarith [mul_lt_mul'' one_lt_sqrt_two pi_gt_three zero_le_one (by norm_num : (0 : ℝ) ≤ 3)]

private lemma exists_pos_quadForm_lt {m : ℕ} {c b : ℤ} (hm : 0 < m) (hc : 0 < c) : ∃ v : Fin 3 → ℤ,
    0 < c * (c * v 0 + b * v 1 + m * v 2) ^ 2 + (c * v 0 + b * v 1) ^ 2 + m * v 1 ^ 2 ∧
    c * (c * v 0 + b * v 1 + m * v 2) ^ 2 + (c * v 0 + b * v 1) ^ 2 + m * v 1 ^ 2 < 2 * m * c := by
  -- Minkowski step: the form is `‖f v‖ ^ 2` for the linear map `f` below, and the region where it
  -- is `< 2 m c` has volume `> 2 ^ 3` by `two_pow_three_lt_volume_preimage_ball`
  have hc' : (0 : ℝ) < c := mod_cast hc
  let f := Matrix.toLin' !![√c * c, √c * b, √c * m; c, b, 0; 0, √m, 0]
  obtain ⟨v, hv0, hv⟩ := exists_ne_zero_int_mem_of_two_pow_card_lt_volume
    (fun x hx ↦ by simpa only [Set.mem_preimage, map_neg, mem_ball_zero_iff, norm_neg] using hx)
    ((convex_ball _ _).linear_preimage
      ((WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).symm.toLinearMap ∘ₗ f))
    (two_pow_three_lt_volume_preimage_ball (b := b) hm hc)
  rw [Set.mem_preimage, mem_ball_zero_iff, EuclideanSpace.norm_eq,
    sqrt_lt_sqrt_iff (by positivity)] at hv
  refine ⟨v, quadForm_pos hm hc hv0, ?_⟩
  rify
  simpa [f, Fin.sum_univ_three, dotProduct, mul_assoc, ← mul_add, mul_pow, sq_sqrt hc'.le] using hv

private lemma not_dvd_of_dvd_binForm_of_squarefree {m p : ℕ} [Fact p.Prime] {b c k R x y : ℤ}
    (hm : Squarefree m) (hp3 : p % 4 = 3) (hmc : (m : ℤ) ∣ c + 1) (hk : b ^ 2 + m = c * k)
    (h : R ^ 2 + (c * x ^ 2 + 2 * b * x * y + k * y ^ 2) = m)
    (hpQ : (p : ℤ) ∣ c * x ^ 2 + 2 * b * x * y + k * y ^ 2) : ¬p ∣ m := by
  rintro ⟨m', rfl⟩
  have hp := Nat.prime_iff_prime_int.1 (Fact.out : p.Prime)
  obtain ⟨Q, hQ⟩ := hpQ
  obtain ⟨j, hj⟩ := hmc
  push_cast at h hk hj
  -- `p ∣ R` and `p ∣ c x + b y`, since both squares vanish modulo `p`
  obtain ⟨R', rfl⟩ := hp.dvd_of_dvd_pow (a := R) (n := 2) ⟨m' - Q, by linear_combination h - hQ⟩
  obtain ⟨A, hA⟩ := hp.dvd_of_dvd_pow (n := 2) (a := c * x + b * y)
    ⟨c * Q - m' * y ^ 2, by linear_combination c * hQ + y ^ 2 * hk⟩
  -- so `p * m' * (c - y ^ 2) = c R ^ 2 + (c x + b y) ^ 2` is divisible by `p ^ 2`, and the
  -- squarefreeness of `m = p * m'` gives `y ^ 2 ≡ c ≡ -1 [ZMOD p]`
  have hdvd : (p : ℤ) ∣ m' * (c - y ^ 2) := ⟨c * R' ^ 2 + A ^ 2, mul_left_cancel₀ hp.ne_zero <| by
    linear_combination -c * h + (c * x + b * y + p * A) * hA - y ^ 2 * hk⟩
  obtain ⟨d, hd⟩ :=
    (Nat.isCoprime_iff_coprime.2 (Nat.coprime_of_squarefree_mul hm)).dvd_of_dvd_mul_left hdvd
  have := (ZMod.intCast_zmod_eq_zero_iff_dvd (y ^ 2 + 1) p).2
    ⟨m' * j - d, by linear_combination hj - hd⟩
  push_cast at this
  exact ZMod.mod_four_ne_three_of_sq_eq_neg_one (eq_neg_of_add_eq_zero_left this) hp3

private lemma isSquare_neg_of_dvd_binForm {m p : ℕ} [Fact p.Prime] {b c k x y : ℤ}
    (hk : b ^ 2 + m = c * k) (hxy : IsCoprime x y)
    (hpQ : (p : ℤ) ∣ c * x ^ 2 + 2 * b * x * y + k * y ^ 2) : IsSquare (-(m : ZMod p)) := by
  -- a prime dividing a primitive value of the form `c x ^ 2 + 2 b x y + k y ^ 2`, of
  -- discriminant `4 (b ^ 2 - c k) = -4 m`, makes `-m` a square modulo `p`
  have e := congrArg (Int.cast : ℤ → ZMod p) hk
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at hpQ
  push_cast at e hpQ
  by_cases hy : (y : ZMod p) = 0
  · have hx : (x : ZMod p) ≠ 0 := fun hx ↦ (Nat.prime_iff_prime_int.1 Fact.out).not_unit <|
      hxy.isUnit_of_dvd' ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hx)
        ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hy)
    have hc : (c : ZMod p) = 0 := by simpa [hy, hx] using hpQ
    exact ⟨b, by linear_combination -e - k * hc⟩
  · refine ⟨(c * x + b * y) / y, ?_⟩
    field_simp
    linear_combination -c * hpQ - y ^ 2 * e

private lemma exists_binForm_eq_sq_add_sq {m : ℕ} {b c k R x y : ℤ} (hm : Squarefree m) (hc : 0 < c)
    (hmc : (m : ℤ) ∣ c + 1) (hk : b ^ 2 + m = c * k)
    (h : R ^ 2 + (c * x ^ 2 + 2 * b * x * y + k * y ^ 2) = m) :
    ∃ u v : ℤ, c * x ^ 2 + 2 * b * x * y + k * y ^ 2 = u ^ 2 + v ^ 2 := by
  -- Arithmetic step: the form `c x ^ 2 + 2 b x y + k y ^ 2` takes the value `m - R ^ 2`.
  -- Write `x = g x'`, `y = g y'` with `x'`, `y'` coprime; `n = c x' ^ 2 + 2 b x' y' + k y' ^ 2`
  -- is nonnegative since `c n = (c x' + b y') ^ 2 + m y' ^ 2`.
  obtain ⟨x', y', hx, hy, hxy⟩ := extract_gcd x y
  generalize gcd x y = g at hx hy
  subst hx hy
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (a := c * x' ^ 2 + 2 * b * x' * y' + k * y' ^ 2)
    ((mul_nonneg_iff_of_pos_left hc).1 <| by
      linear_combination add_nonneg (sq_nonneg (c * x' + b * y'))
        (mul_nonneg m.cast_nonneg (sq_nonneg y')) + y' ^ 2 * hk)
  -- by the two squares theorem it suffices that no prime `p ≡ 3 [MOD 4]` divides `n`
  suffices H : ∀ p ∈ n.primeFactors, p % 4 ≠ 3 by
    obtain ⟨u, v, huv⟩ := Nat.eq_sq_add_sq_iff.2 fun p hp hp3 ↦ (H p hp hp3).elim
    have huv : (n : ℤ) = u ^ 2 + v ^ 2 := mod_cast huv
    exact ⟨g * u, g * v, by linear_combination g ^ 2 * (hn + huv)⟩
  intro p hp hp3
  have := Fact.mk (Nat.prime_of_mem_primeFactors hp)
  have hpn : (p : ℤ) ∣ c * x' ^ 2 + 2 * b * x' * y' + k * y' ^ 2 :=
    hn ▸ Int.natCast_dvd_natCast.2 (Nat.dvd_of_mem_primeFactors hp)
  have hpQ : (p : ℤ) ∣ c * (g * x') ^ 2 + 2 * b * (g * x') * (g * y') + k * (g * y') ^ 2 :=
    hpn.trans ⟨g ^ 2, by ring⟩
  by_cases hpm : p ∣ m
  · -- `p ∣ m`: squarefreeness of `m` gives `(g y') ^ 2 ≡ c ≡ -1 [ZMOD p]`
    exact not_dvd_of_dvd_binForm_of_squarefree hm hp3 hmc hk h hpQ hpm
  · -- `p ∤ m`: `m ≡ R ^ 2` is a nonzero square modulo `p`, forcing `p ∣ x'` and `p ∣ y'`
    obtain ⟨r, hr⟩ := isSquare_neg_of_dvd_binForm hk ((gcd_isUnit_iff x' y').1 hxy) hpn
    have hR := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).2 (eq_sub_of_add_eq' h ▸ hpQ)
    push_cast at hR
    refine ZMod.mod_four_ne_three_of_sq_eq_neg_sq' (x := r) (y := R) (fun h0 ↦ hpm ?_)
      (by linear_combination -hr - hR) hp3
    exact (ZMod.natCast_eq_zero_iff m p).1 (by linear_combination hR + R * h0)

private lemma exists_sq_add_binForm_eq {m : ℕ} {c b k : ℤ} (hm : 0 < m) (hc : 0 < c)
    (hmc : (m : ℤ) ∣ c + 1) (hk : b ^ 2 + m = c * k) :
    ∃ R x y : ℤ, R ^ 2 + (c * x ^ 2 + 2 * b * x * y + k * y ^ 2) = m := by
  -- Minkowski gives `v` with `0 < c (R ^ 2 + w) < 2 m c`, where `R = c v₀ + b v₁ + m v₂` and
  -- `w = c v₀ ^ 2 + 2 b v₀ v₁ + k v₁ ^ 2`; as `m ∣ R ^ 2 + w`, this forces `R ^ 2 + w = m`
  obtain ⟨v, hpos, hlt⟩ := exists_pos_quadForm_lt (b := b) hm hc
  obtain ⟨j, hj⟩ := hmc
  obtain ⟨e, he⟩ : (m : ℤ) ∣ (c * v 0 + b * v 1 + m * v 2) ^ 2 +
      (c * v 0 ^ 2 + 2 * b * v 0 * v 1 + k * v 1 ^ 2) :=
    ⟨j * (c * v 0 ^ 2 + 2 * b * v 0 * v 1 + k * v 1 ^ 2) + 2 * (c * v 0 + b * v 1) * v 2 +
      m * v 2 ^ 2 - v 1 ^ 2,
      by linear_combination (c * v 0 ^ 2 + 2 * b * v 0 * v 1 + k * v 1 ^ 2) * hj + v 1 ^ 2 * hk⟩
  have hcm : 0 < c * m := by positivity
  have h1 : 0 < c * m * e := by linear_combination hpos + c * he + v 1 ^ 2 * hk
  have h2 : c * m * e < c * m * 2 := by linear_combination hlt - c * he - v 1 ^ 2 * hk
  obtain rfl : e = 1 := by
    have := pos_of_mul_pos_right h1 hcm.le
    have := lt_of_mul_lt_mul_left h2 hcm.le
    omega
  exact ⟨_, _, _, he.trans (mul_one _)⟩

/-- **Davenport's method**: a squarefree `m` is a sum of three squares as soon as there are
integers `0 < c` and `b` with `m ∣ c + 1` and `c ∣ b ^ 2 + m`.

This is the geometry-of-numbers core of Ankeny's proof of Legendre's three squares theorem:
`Nat.eq_sq_add_sq_add_sq_of_squarefree` produces suitable `c` and `b` from a prime in an
arithmetic progression (Dirichlet's theorem). -/
theorem Nat.eq_sq_add_sq_add_sq_of_dvd {m : ℕ} {c b : ℤ} (hm : Squarefree m) (hc : 0 < c)
    (hmc : (m : ℤ) ∣ c + 1) (hcb : c ∣ b ^ 2 + m) : ∃ x y z : ℤ, m = x ^ 2 + y ^ 2 + z ^ 2 := by
  obtain ⟨k, hk⟩ := hcb
  -- Minkowski: `R ^ 2 + (c x ^ 2 + 2 b x y + k y ^ 2) = m` for some integers `R`, `x`, `y`
  obtain ⟨R, x, y, h⟩ := exists_sq_add_binForm_eq (pos_of_ne_zero hm.ne_zero) hc hmc hk
  -- the binary form `c x ^ 2 + 2 b x y + k y ^ 2` then takes a value which is a sum of two squares
  obtain ⟨u, w, huw⟩ := exists_binForm_eq_sq_add_sq hm hc hmc hk h
  exact ⟨R, u, w, by linear_combination huw - h⟩

private lemma exists_dvd_add_one_dvd_sq_add {m a d : ℕ} (ha : a.Coprime (4 * m))
    (hJ : jacobiSym (-m) a = 1) (hd : (m : ℤ) ∣ d * a + 1) (hd' : d = 1 ∨ d = 2 ∧ Odd m) :
    ∃ c b : ℤ, 0 < c ∧ (m : ℤ) ∣ c + 1 ∧ c ∣ b ^ 2 + m := by
  -- Dirichlet step: a prime `q ≡ a [MOD 4 m]` gives `c = d q` as in
  -- `Nat.eq_sq_add_sq_add_sq_of_dvd`; like `a`, it is coprime to `4 m`, hence odd
  obtain ⟨q, -, hq, hqa⟩ := Nat.forall_exists_prime_gt_and_modEq 0 (by rintro h; simp_all) ha
  have ha2 : Odd a := (ha.coprime_dvd_right ⟨2 * m, by ring⟩).odd_of_right
  have hq2 : Odd q :=
    Nat.coprime_two_right.1 <| .coprime_dvd_right ⟨2 * m, by ring⟩ (hqa.gcd_eq.trans ha)
  have := Fact.mk hq
  -- `J(-m | ·)` only depends on the residue modulo `4 m`, so `-m` is a square modulo `q`
  obtain ⟨r, hr⟩ := ZMod.isSquare_of_jacobiSym_eq_one (p := q) (a := -m) <| by
    rw [jacobiSym.mod_right _ hq2, ← hJ, jacobiSym.mod_right _ ha2, Int.natAbs_neg,
      Int.natAbs_natCast, hqa]
  obtain ⟨b, rfl⟩ := ZMod.intCast_surjective r
  have hb : (q : ℤ) ∣ b ^ 2 + m := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 (by simp [sq, ← hr])
  -- `q ≡ a [MOD m]`, so `m ∣ d q + 1`
  have hmc : (m : ℤ) ∣ d * q + 1 :=
    mod_cast (((hqa.of_mul_left 4).mul_left d).add_right 1).dvd_iff dvd_rfl |>.2 (mod_cast hd)
  rcases hd' with rfl | ⟨rfl, hm2⟩
  · exact ⟨q, b, mod_cast hq.pos, by simpa using hmc, hb⟩
  -- For `d = 2`, replace `b` by `b * (q + 1) + q`, which is odd and congruent to `b` modulo `q`.
  refine ⟨2 * q, b * (q + 1) + q, by simpa using hq.pos, mod_cast hmc,
    IsCoprime.mul_dvd (Nat.isCoprime_iff_coprime.2 hq2.coprime_two_left) ?_ ?_⟩
  · replace hq2 : Odd (q : ℤ) := mod_cast hq2
    exact (((hq2.add_one.mul_left _).add_odd hq2).pow.add_odd (mod_cast hm2)).two_dvd
  · exact (((Int.modEq_iff_dvd.2 ⟨b + 1, by ring⟩).pow 2).add_right _).dvd_iff.1 hb

private lemma exists_dvd_add_one_dvd_sq_add_of_not_four_dvd {m : ℕ} (h4 : ¬4 ∣ m) (h7 : m % 8 ≠ 7) :
    ∃ c b : ℤ, 0 < c ∧ (m : ℤ) ∣ c + 1 ∧ c ∣ b ^ 2 + m := by
  rcases (by lia : m % 4 = 1 ∨ m % 4 = 2 ∨ m % 8 = 3) with h | h
  · -- `m = 4 n + 1`: take `a = 8 n + 1 = 2 m - 1` and `d = 1`; then `-2 m ≡ -1 [ZMOD a]`, and
    -- `J(-1 | a) = J(2 | a) = 1` as `a ≡ 1 [MOD 8]`
    obtain ⟨n, rfl⟩ : ∃ n, m = 4 * n + 1 := ⟨m / 4, by lia⟩
    have ha : Odd (8 * n + 1) := ⟨4 * n, by ring⟩
    refine exists_dvd_add_one_dvd_sq_add (a := 8 * n + 1) (d := 1)
      (Nat.isCoprime_iff_coprime.1 ⟨8 * n + 1, -4 * n, by push_cast; ring⟩) ?_
      ⟨2, by push_cast; ring⟩ (.inl rfl)
    have h1 := jacobiSym.mul_left (-(4 * n + 1 : ℕ)) 2 (8 * n + 1)
    rwa [jacobiSym.mod_left' (a₂ := -1) (Int.modEq_iff_dvd.2 ⟨1, by push_cast; ring⟩),
      jacobiSym.at_neg_one ha, jacobiSym.at_two ha, ZMod.χ₄_nat_one_mod_four (by omega),
      ZMod.χ₈_nat_eq_if_mod_eight, if_neg (by lia), if_pos (by lia), mul_one, eq_comm] at h1
  -- `m = 4 n + 2` or `m = 8 n + 3`: then `m = d a + 1` with `a = 4 n + 1` and `d = 1` or `d = 2`,
  -- so `-m ≡ -1 [ZMOD a]` and `J(-m | a) = χ₄ a = 1`
  obtain ⟨d, n, rfl, hd⟩ : ∃ d n, m = d * (4 * n + 1) + 1 ∧ (d = 1 ∨ d = 2 ∧ Odd m) := by
    rcases h with h | h
    exacts [⟨1, m / 4, by lia, .inl rfl⟩, ⟨2, m / 8, by lia, .inr ⟨rfl, m / 2, by lia⟩⟩]
  exact exists_dvd_add_one_dvd_sq_add (a := 4 * n + 1)
    (Nat.isCoprime_iff_coprime.1 ⟨4 * d * n + 1, -n, by push_cast; ring⟩)
    (by rw [jacobiSym.mod_left' (a₂ := -1) (Int.modEq_iff_dvd.2 ⟨d, by push_cast; ring⟩),
      jacobiSym.at_neg_one ⟨2 * n, by ring⟩, ZMod.χ₄_nat_one_mod_four (by omega)])
    (mod_cast dvd_rfl) hd

/-- A squarefree natural number `m` with `m % 8 ≠ 7` is a sum of three squares.

Unlike `Nat.eq_sq_add_sq_add_sq_of_dvd`, the squares are of natural numbers and no auxiliary
integers `c`, `b` are needed. For squarefree `m` the condition `m % 8 ≠ 7` is also necessary; see
`Nat.eq_sq_add_sq_add_sq_iff` for the characterisation of all sums of three squares. -/
theorem Nat.eq_sq_add_sq_add_sq_of_squarefree {m : ℕ} (hm : Squarefree m) (h : m % 8 ≠ 7) :
    ∃ x y z : ℕ, m = x ^ 2 + y ^ 2 + z ^ 2 := by
  -- squarefreeness rules out `4 ∣ m`, which leaves `m % 4 ∈ {1, 2}` or `m % 8 = 3`
  obtain ⟨c, b, hc, hmc, hcb⟩ :=
    exists_dvd_add_one_dvd_sq_add_of_not_four_dvd (fun h ↦ by simpa using hm 2 h) h
  obtain ⟨x, y, z, h⟩ := eq_sq_add_sq_add_sq_of_dvd hm hc hmc hcb
  exact ⟨x.natAbs, y.natAbs, z.natAbs, by simpa [← Int.natCast_inj] using h⟩

/-- A natural number of the form `4 ^ a * (8 * k + 7)` is not a sum of three squares.

This is the easy direction of Legendre's three squares theorem `Nat.eq_sq_add_sq_add_sq_iff`,
stated with explicit `x`, `y`, `z` so that it refutes a given representation directly. -/
theorem Nat.four_pow_mul_ne_sq_add_sq_add_sq (a k x y z : ℕ) :
    4 ^ a * (8 * k + 7) ≠ x ^ 2 + y ^ 2 + z ^ 2 := by
  have h8 (n : ℕ) : n ^ 2 % 8 = 0 ∨ n ^ 2 % 8 = 1 ∨ n ^ 2 % 8 = 4 := by
    have := n.mod_lt (show 0 < 8 by norm_num)
    rw [Nat.pow_mod]
    interval_cases n % 8 <;> simp
  have h2 (n : ℕ) : n ^ 2 % 4 = n % 2 := by
    rw [Nat.pow_mod, ← Nat.mod_mod_of_dvd n (show 2 ∣ 4 by norm_num)]
    have := n.mod_lt (show 0 < 4 by norm_num)
    interval_cases n % 4 <;> simp
  intro h
  induction a generalizing x y z with
  | zero =>
    -- squares mod 8 lie in `{0, 1, 4}`, so no sum of three of them is `7`
    have := h8 x
    have := h8 y
    have := h8 z
    omega
  | succ a ih =>
    -- squares mod 4 detect parity, so `x`, `y`, `z` are even; divide by `4` and use the
    -- induction hypothesis
    have h4 : 4 ∣ x ^ 2 + y ^ 2 + z ^ 2 := ⟨4 ^ a * (8 * k + 7), by rw [← h]; ring⟩
    obtain ⟨⟨x, rfl⟩, ⟨y, rfl⟩, ⟨z, rfl⟩⟩ : 2 ∣ x ∧ 2 ∣ y ∧ 2 ∣ z := by
      have := h2 x
      have := h2 y
      have := h2 z
      clear h ih
      omega
    exact ih x y z (Nat.eq_of_mul_eq_mul_left four_pos (by rw [← mul_assoc, ← pow_succ', h]; ring))

private lemma eq_sq_add_sq_add_sq_of_not_four_dvd {n : ℕ} (h4 : ¬4 ∣ n) (h7 : n % 8 ≠ 7) :
    ∃ x y z, n = x ^ 2 + y ^ 2 + z ^ 2 := by
  -- write `n = s ^ 2 * r` with `r` squarefree; `s` is odd since `4 ∤ n`
  obtain ⟨r, s, rfl, hr⟩ := Nat.sq_mul_squarefree n
  obtain ⟨t, rfl | rfl⟩ := s.even_or_odd'
  · exact absurd ⟨t ^ 2 * r, by ring⟩ h4
  -- `s ^ 2 ≡ 1 [MOD 8]`, so `r ≡ n [MOD 8]` and `r % 8 ≠ 7`
  obtain ⟨u, hu⟩ := Nat.even_mul_succ_self t
  obtain ⟨x, y, z, h⟩ := Nat.eq_sq_add_sq_add_sq_of_squarefree hr fun h' ↦ h7 <| by
    rwa [show (2 * t + 1) ^ 2 * r = 8 * (u * r) + r by linear_combination 4 * r * hu,
      Nat.mul_add_mod_self_left]
  exact ⟨(2 * t + 1) * x, (2 * t + 1) * y, (2 * t + 1) * z, h ▸ by ring⟩

/-- **Legendre's three squares theorem**: a natural number is a sum of three squares if and only
if it is not of the form `4 ^ a * (8 * k + 7)`.

This is the three-squares analogue of `Nat.eq_sq_add_sq_iff`. To refute a specific representation
use `Nat.four_pow_mul_ne_sq_add_sq_add_sq`; for squarefree `n` the simpler criterion `n % 8 ≠ 7`
is `Nat.eq_sq_add_sq_add_sq_of_squarefree`. -/
theorem Nat.eq_sq_add_sq_add_sq_iff {n : ℕ} :
    (∃ x y z, n = x ^ 2 + y ^ 2 + z ^ 2) ↔ ∀ a k, n ≠ 4 ^ a * (8 * k + 7) := by
  refine ⟨fun ⟨x, y, z, h⟩ a k h' ↦ four_pow_mul_ne_sq_add_sq_add_sq a k x y z (h' ▸ h), fun h ↦ ?_⟩
  obtain rfl | hn := eq_or_ne n 0
  · exact ⟨0, 0, 0, rfl⟩
  -- write `n = 4 ^ a * m` with `4 ∤ m`; then `m % 8 ≠ 7`, so `m` is a sum of three squares
  obtain ⟨a, m, h4, rfl⟩ := exists_eq_pow_mul_and_not_dvd hn 4 (by decide)
  obtain ⟨x, y, z, rfl⟩ := eq_sq_add_sq_add_sq_of_not_four_dvd h4 fun h7 ↦ h a (m / 8) (by lia)
  exact ⟨2 ^ a * x, 2 ^ a * y, 2 ^ a * z,
    by linear_combination (x ^ 2 + y ^ 2 + z ^ 2) * pow_right_comm 2 2 a⟩
