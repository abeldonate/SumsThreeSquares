/-
Copyright (c) 2026 Abel Doñate Muñoz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abel Doñate Muñoz
-/
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
  are integers `c > 0` and `b` with `m ∣ c + 1` and `c ∣ b ^ 2 + m`.
* `Nat.eq_sq_add_sq_add_sq_of_squarefree`: a squarefree `m` with `m % 8 ≠ 7` is a sum of three
  squares.
* `Nat.eq_sq_add_sq_add_sq_iff`: **Legendre's three squares theorem**.

## Implementation notes

The blueprint chooses a prime `q` with prescribed quadratic characters and an auxiliary `t` with
`2 q t ^ 2 ≡ -1 [ZMOD m]`. Choosing instead `q` in a suitable residue class modulo `4 m`, we can
take `t = 1`: writing `c = q` (or `c = 2 q` when `m % 8 = 3`) we get `m ∣ c + 1`, and both cases of
the blueprint become instances of `Nat.eq_sq_add_sq_add_sq_of_dvd`.

## References

* N. C. Ankeny, *Sums of three squares*, Proc. Amer. Math. Soc. 8 (1957), 316–319.
* H. Davenport, *The geometry of numbers*, Math. Gazette 31 (1947), 206–210.
-/

open MeasureTheory Metric Real

/-- Minkowski step: the positive definite ternary form
`c (c x + b y + m z) ^ 2 + (c x + b y) ^ 2 + m y ^ 2` takes a value in the open interval
`(0, 2 m c)` at an integral point. It is the squared norm of a linear map of determinant
`m c √(m c)`, so the volume of the region where it is `< 2 m c` is `8 √2 π / 3 > 8`. -/
private lemma exists_pos_quadForm_lt {m : ℕ} {c b : ℤ} (hm : 0 < m) (hc : 0 < c) :
    ∃ v : Fin 3 → ℤ, 0 < c * (c * v 0 + b * v 1 + m * v 2) ^ 2 + (c * v 0 + b * v 1) ^ 2 +
      m * v 1 ^ 2 ∧ c * (c * v 0 + b * v 1 + m * v 2) ^ 2 + (c * v 0 + b * v 1) ^ 2 +
      m * v 1 ^ 2 < 2 * m * c := by
  have hc' : (0 : ℝ) < c := mod_cast hc
  have hm' : (0 : ℝ) < m := mod_cast hm
  let f := Matrix.toLin' !![√c * c, √c * b, √c * m; c, b, 0; 0, √m, 0]
  have hdet : LinearMap.det f = √c * √m * m * c := by simp [f, Matrix.det_fin_three]; ring
  have hvol : 2 ^ 3 < volume (f ⁻¹' (WithLp.toLp 2 ⁻¹' ball 0 √(2 * m * c))) := by
    rw [Measure.addHaar_preimage_linearMap _ (by rw [hdet]; positivity),
      (PiLp.volume_preserving_toLp _).measure_preimage measurableSet_ball.nullMeasurableSet,
      EuclideanSpace.volume_ball_fin_three, hdet, ← ENNReal.ofReal_pow (sqrt_nonneg _),
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (abs_nonneg _),
      show (2 : ENNReal) ^ 3 = .ofReal 8 by norm_num, ENNReal.ofReal_lt_ofReal_iff (by positivity),
      abs_of_pos (by positivity), pow_succ, sq_sqrt (by positivity), sqrt_mul' _ hc'.le,
      sqrt_mul' _ hm'.le]
    field_simp
    nlinarith [pi_gt_three, one_lt_sqrt_two]
  obtain ⟨v, hv0, hv⟩ := exists_ne_zero_int_mem_of_two_pow_card_lt_volume
    (fun x hx ↦ by simpa using hx) ((convex_ball _ _).linear_preimage
      ((WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).symm.toLinearMap ∘ₗ f)) hvol
  rw [Set.mem_preimage, mem_ball_zero_iff, EuclideanSpace.norm_eq,
    sqrt_lt_sqrt_iff (by positivity)] at hv
  refine ⟨v, ?_, ?_⟩
  · rcases eq_or_ne (v 1) 0 with h1 | h1
    · rcases eq_or_ne (v 0) 0 with h0 | h0
      · have h2 : v 2 ≠ 0 := fun h2 ↦ hv0 (funext fun i ↦ by fin_cases i <;> assumption)
        simp only [h0, h1, mul_zero, zero_add]; positivity
      · simp only [h1, mul_zero, add_zero]; positivity
    · positivity
  · rw [← Int.cast_lt (R := ℝ)]
    push_cast
    simpa [f, Fin.sum_univ_three, dotProduct, mul_assoc, ← mul_add, mul_pow, sq_sqrt hc'.le]
      using hv

/-- Arithmetic step: if `R ^ 2 + (c x ^ 2 + 2 b x y + k y ^ 2) = m` where `b ^ 2 + m = c k`,
`m ∣ c + 1` and `m` is squarefree, then the binary form `c x ^ 2 + 2 b x y + k y ^ 2` is a sum of
two squares. -/
private lemma exists_binForm_eq_sq_add_sq {m : ℕ} {b c k R x y : ℤ} (hm : Squarefree m)
    (hc : 0 < c) (hmc : (m : ℤ) ∣ c + 1) (hk : b ^ 2 + m = c * k)
    (h : R ^ 2 + (c * x ^ 2 + 2 * b * x * y + k * y ^ 2) = m) :
    ∃ u v : ℤ, c * x ^ 2 + 2 * b * x * y + k * y ^ 2 = u ^ 2 + v ^ 2 := by
  have hw (x y : ℤ) : c * (c * x ^ 2 + 2 * b * x * y + k * y ^ 2) =
      (c * x + b * y) ^ 2 + m * y ^ 2 := by linear_combination -y ^ 2 * hk
  obtain ⟨j, hj⟩ := hmc
  obtain ⟨x', y', hx, hy, hxy⟩ := extract_gcd x y
  generalize gcd x y = g at hx hy
  subst hx hy
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (a := c * x' ^ 2 + 2 * b * x' * y' + k * y' ^ 2)
    ((mul_nonneg_iff_of_pos_left hc).1 (by rw [hw]; positivity))
  suffices H : ∀ p ∈ n.primeFactors, p % 4 ≠ 3 by
    obtain ⟨u, v, huv⟩ := Nat.eq_sq_add_sq_iff.2 fun p hp hp3 ↦ (H p hp hp3).elim
    have huv : (n : ℤ) = u ^ 2 + v ^ 2 := mod_cast huv
    exact ⟨g * u, g * v, by linear_combination g ^ 2 * (hn + huv)⟩
  intro p hp hp3
  have hp' := Nat.prime_of_mem_primeFactors hp
  have := Fact.mk hp'
  have key (X Y : ZMod p) (h : X ^ 2 + Y ^ 2 = 0) : Y = 0 := by
    by_contra hY
    exact ZMod.mod_four_ne_three_of_sq_eq_neg_sq' (x := X) hY (by linear_combination h) hp3
  have e1 := congrArg (Int.cast : ℤ → ZMod p) h
  have e2 := congrArg (Int.cast : ℤ → ZMod p) hn
  have e3 := congrArg (Int.cast : ℤ → ZMod p) hk
  have e4 := congrArg (Int.cast : ℤ → ZMod p) hj
  have e5 := congrArg (Int.cast : ℤ → ZMod p) (hw x' y')
  have e6 := congrArg (Int.cast : ℤ → ZMod p) (hw (g * x') (g * y'))
  push_cast [(ZMod.natCast_eq_zero_iff n p).2 (Nat.dvd_of_mem_primeFactors hp)] at e1 e2 e3 e4 e5 e6
  have hR : (R : ZMod p) ^ 2 = m := by linear_combination e1 - g ^ 2 * e2
  by_cases hpm : (m : ZMod p) = 0
  · -- `p ∣ m`: then `p ∣ R` and `p ∣ c g x' + b g y'`, and squarefreeness of `m` gives
    -- `(g y') ^ 2 ≡ c ≡ -1 [ZMOD p]`.
    obtain ⟨R', hR'⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd R p).1
      ((pow_eq_zero_iff two_ne_zero).1 (hR.trans hpm))
    obtain ⟨A', hA'⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd (c * (g * x') + b * (g * y')) p).1 <| by
      push_cast
      exact (pow_eq_zero_iff two_ne_zero).1
        (by linear_combination -e6 + c * g ^ 2 * e2 - (g * y') ^ 2 * hpm)
    obtain ⟨m', hm'⟩ := (ZMod.natCast_eq_zero_iff m p).1 hpm
    have hdvd : (p : ℤ) ∣ m' * (c - (g * y') ^ 2) := ⟨c * R' ^ 2 + A' ^ 2,
      mul_left_cancel₀ (Int.natCast_ne_zero.2 hp'.ne_zero) <| by
        have := hw (g * x') (g * y')
        rw [hA'] at this
        rw [hR'] at h
        push_cast [hm'] at h this
        linear_combination this - c * h⟩
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).2 <| (Nat.isCoprime_iff_coprime.2
      (Nat.coprime_of_squarefree_mul (hm' ▸ hm))).dvd_of_dvd_mul_left hdvd
    push_cast at this
    exact one_ne_zero (key (g * y') 1 (by linear_combination e4 - this + j * hpm))
  · -- `p ∤ m`: then `m ≡ R ^ 2` is a nonzero square modulo `p`, which forces `p ∣ x'` and `p ∣ y'`.
    have hR0 : (R : ZMod p) ≠ 0 := fun h0 ↦ hpm (by rw [← hR, h0]; ring)
    have hc0 : (c : ZMod p) ≠ 0 := fun h0 ↦ hR0 (key b R (by linear_combination e3 + hR + k * h0))
    have hy0 : (y' : ZMod p) = 0 := by
      simpa [hR0] using
        key (c * x' + b * y') (R * y') (by linear_combination hR * y' ^ 2 - e5 + c * e2)
    have hx0 : (x' : ZMod p) = 0 := by
      have : (c : ZMod p) * x' ^ 2 = 0 := by simpa [hy0] using e2
      simpa [hc0] using this
    exact (Nat.prime_iff_prime_int.1 hp').not_unit <| isUnit_of_dvd_unit
      (dvd_gcd ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hx0)
        ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hy0)) hxy

/-- **Davenport's method**: a squarefree `m` is a sum of three squares as soon as there are
integers `c > 0` and `b` with `m ∣ c + 1` and `c ∣ b ^ 2 + m`. -/
theorem Nat.eq_sq_add_sq_add_sq_of_dvd {m : ℕ} {c b : ℤ} (hm : Squarefree m) (hc : 0 < c)
    (hmc : (m : ℤ) ∣ c + 1) (hcb : c ∣ b ^ 2 + m) : ∃ x y z : ℤ, m = x ^ 2 + y ^ 2 + z ^ 2 := by
  obtain ⟨k, hk⟩ := hcb
  have hm0 := Nat.pos_of_ne_zero hm.ne_zero
  obtain ⟨v, hpos, hlt⟩ := exists_pos_quadForm_lt (b := b) hm0 hc
  have hw : c * (c * v 0 ^ 2 + 2 * b * v 0 * v 1 + k * v 1 ^ 2) =
      (c * v 0 + b * v 1) ^ 2 + m * v 1 ^ 2 := by linear_combination -v 1 ^ 2 * hk
  obtain ⟨j, hj⟩ := hmc
  obtain ⟨e, he⟩ : (m : ℤ) ∣ (c * v 0 + b * v 1 + m * v 2) ^ 2 +
      (c * v 0 ^ 2 + 2 * b * v 0 * v 1 + k * v 1 ^ 2) :=
    ⟨j * (c * v 0 ^ 2 + 2 * b * v 0 * v 1 + k * v 1 ^ 2) + 2 * (c * v 0 + b * v 1) * v 2 +
      m * v 2 ^ 2 - v 1 ^ 2,
      by linear_combination (c * v 0 ^ 2 + 2 * b * v 0 * v 1 + k * v 1 ^ 2) * hj - hw⟩
  obtain rfl : e = 1 := by
    have : 0 < e := by nlinarith
    have : e < 2 := by nlinarith
    omega
  obtain ⟨u, w, huw⟩ := exists_binForm_eq_sq_add_sq hm hc ⟨j, hj⟩ hk (he.trans (mul_one _))
  exact ⟨c * v 0 + b * v 1 + m * v 2, u, w, by linear_combination huw - he⟩

/-- Dirichlet step: given `a` coprime to `4 m` with `J(-m | a) = 1` and `m ∣ d a + 1` for
`d = 1`, or `d = 2` and `m` odd, a prime `q ≡ a [MOD 4 m]` gives `c = d q` as in
`Nat.eq_sq_add_sq_add_sq_of_dvd`. -/
private lemma exists_dvd_add_one_dvd_sq_add {m a d : ℕ} (hm : 0 < m) (ha : a.Coprime (4 * m))
    (hJ : jacobiSym (-m) a = 1) (hd : (m : ℤ) ∣ d * a + 1) (hd' : d = 1 ∨ d = 2 ∧ Odd m) :
    ∃ c b : ℤ, 0 < c ∧ (m : ℤ) ∣ c + 1 ∧ c ∣ b ^ 2 + m := by
  have : NeZero (4 * m) := ⟨by positivity⟩
  obtain ⟨q, -, hq, hqa⟩ :=
    Nat.forall_exists_prime_gt_and_eq_mod ((ZMod.isUnit_iff_coprime a (4 * m)).2 ha) 0
  have hqa := (ZMod.natCast_eq_natCast_iff _ _ _).1 hqa
  have ha2 : Odd a := Nat.coprime_two_right.1 (ha.coprime_dvd_right ⟨2 * m, by ring⟩)
  have hq2 : Odd q :=
    Nat.odd_iff.2 <| Eq.trans (Nat.ModEq.of_dvd ⟨2 * m, by ring⟩ hqa) (Nat.odd_iff.1 ha2)
  have := Fact.mk hq
  have h1 := jacobiSym.mod_right (-m) hq2
  have h2 := jacobiSym.mod_right (-m) ha2
  simp only [Int.natAbs_neg, Int.natAbs_natCast] at h1 h2
  obtain ⟨r, hr⟩ := ZMod.isSquare_of_jacobiSym_eq_one (p := q) (a := -m) <| by
    rwa [h1, (hqa : q % (4 * m) = a % (4 * m)), ← h2]
  have hb : (q : ℤ) ∣ (r.val : ℤ) ^ 2 + m := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 <| by
    push_cast at hr ⊢
    rw [ZMod.natCast_zmod_val]
    linear_combination -hr
  obtain ⟨e, he⟩ := Nat.modEq_iff_dvd.1 hqa.symm
  obtain ⟨l, hl⟩ := hd
  have hmc : (m : ℤ) ∣ d * q + 1 :=
    ⟨l + 4 * d * e, by push_cast at he; linear_combination d * he + hl⟩
  rcases hd' with rfl | ⟨rfl, hm2⟩
  · exact ⟨q, r.val, mod_cast hq.pos, by simpa using hmc, hb⟩
  -- For `d = 2`, replace `r.val` by `r.val * (q + 1) + q`, which is odd and congruent modulo `q`.
  have hq2 : Odd (q : ℤ) := mod_cast hq2
  obtain ⟨s, hs⟩ := id hq2
  refine ⟨2 * q, r.val * (q + 1) + q, by have := hq.pos; positivity, mod_cast hmc,
    IsCoprime.mul_dvd ⟨-s, 1, by linear_combination hs⟩ ?_ ?_⟩
  · exact (((hq2.add_one.mul_left _).add_odd hq2).pow.add_odd (mod_cast hm2)).two_dvd
  · exact (hb.add (dvd_mul_right _ ((r.val : ℤ) ^ 2 * (q + 2) + 2 * r.val * (q + 1) + q))).trans
      (dvd_of_eq (by ring))

/-- A squarefree natural number `m` with `m % 8 ≠ 7` is a sum of three squares. -/
theorem Nat.eq_sq_add_sq_add_sq_of_squarefree {m : ℕ} (hm : Squarefree m) (h : m % 8 ≠ 7) :
    ∃ x y z : ℕ, m = x ^ 2 + y ^ 2 + z ^ 2 := by
  have h4 : ¬ 2 * 2 ∣ m := fun h ↦ by simpa using hm 2 h
  have hm0 := pos_of_ne_zero hm.ne_zero
  obtain ⟨c, b, hc, hmc, hcb⟩ : ∃ c b : ℤ, 0 < c ∧ (m : ℤ) ∣ c + 1 ∧ c ∣ b ^ 2 + m := by
    rcases (by omega : m % 4 = 1 ∨ m % 4 = 2 ∨ m % 8 = 3) with h | h | h
    · obtain ⟨n, rfl⟩ : ∃ n, m = 4 * n + 1 := ⟨m / 4, by omega⟩
      have ha : Odd (8 * n + 1) := ⟨4 * n, by ring⟩
      refine exists_dvd_add_one_dvd_sq_add (a := 8 * n + 1) (d := 1) hm0
        (isCoprime_iff_coprime.1 ⟨8 * n + 1, -4 * n, by push_cast; ring⟩) ?_
        ⟨2, by push_cast; ring⟩ (.inl rfl)
      have h1 := jacobiSym.mul_left (-(4 * n + 1 : ℕ)) 2 (8 * n + 1)
      rwa [jacobiSym.mod_left' (a₂ := -1) (Int.modEq_iff_dvd.2 ⟨1, by push_cast; ring⟩),
        jacobiSym.at_neg_one ha, jacobiSym.at_two ha, ZMod.χ₄_nat_one_mod_four (by omega),
        ZMod.χ₈_nat_eq_if_mod_eight, if_neg (by omega), if_pos (by omega), mul_one, eq_comm] at h1
    · obtain ⟨n, rfl⟩ : ∃ n, m = 4 * n + 2 := ⟨m / 4, by omega⟩
      exact exists_dvd_add_one_dvd_sq_add (a := 4 * n + 1) (d := 1) hm0
        (isCoprime_iff_coprime.1 ⟨4 * n + 1, -n, by push_cast; ring⟩)
        (by rw [jacobiSym.mod_left' (a₂ := -1) (Int.modEq_iff_dvd.2 ⟨1, by push_cast; ring⟩),
          jacobiSym.at_neg_one ⟨2 * n, by ring⟩, ZMod.χ₄_nat_one_mod_four (by omega)])
        ⟨1, by push_cast; ring⟩ (.inl rfl)
    · obtain ⟨n, rfl⟩ : ∃ n, m = 8 * n + 3 := ⟨m / 8, by omega⟩
      exact exists_dvd_add_one_dvd_sq_add (a := 4 * n + 1) (d := 2) hm0
        (isCoprime_iff_coprime.1 ⟨8 * n + 1, -n, by push_cast; ring⟩)
        (by rw [jacobiSym.mod_left' (a₂ := -1) (Int.modEq_iff_dvd.2 ⟨2, by push_cast; ring⟩),
          jacobiSym.at_neg_one ⟨2 * n, by ring⟩, ZMod.χ₄_nat_one_mod_four (by omega)])
        ⟨1, by push_cast; ring⟩ (.inr ⟨rfl, 4 * n + 1, by ring⟩)
  obtain ⟨x, y, z, h⟩ := eq_sq_add_sq_add_sq_of_dvd hm hc hmc hcb
  exact ⟨x.natAbs, y.natAbs, z.natAbs, by zify; simpa using h⟩

/-- A natural number of the form `4 ^ a * (8 * k + 7)` is not a sum of three squares. -/
theorem Nat.four_pow_mul_ne_sq_add_sq_add_sq (a k x y z : ℕ) :
    4 ^ a * (8 * k + 7) ≠ x ^ 2 + y ^ 2 + z ^ 2 := by
  induction a generalizing x y z with
  | zero =>
    intro h
    have := congrArg (Nat.cast : ℕ → ZMod 8) h
    push_cast at this
    generalize (x : ZMod 8) = x, (y : ZMod 8) = y, (z : ZMod 8) = z, (k : ZMod 8) = k at this
    revert x y z k
    decide
  | succ a ih =>
    intro h
    rcases Nat.even_or_odd' x with ⟨x, rfl | rfl⟩ <;>
      rcases Nat.even_or_odd' y with ⟨y, rfl | rfl⟩ <;>
      rcases Nat.even_or_odd' z with ⟨z, rfl | rfl⟩ <;> ring_nf at h <;> try omega
    exact ih x y z (by ring_nf; omega)

/-- **Legendre's three squares theorem**: a natural number is a sum of three squares if and only
if it is not of the form `4 ^ a * (8 * k + 7)`. -/
theorem Nat.eq_sq_add_sq_add_sq_iff {n : ℕ} :
    (∃ x y z, n = x ^ 2 + y ^ 2 + z ^ 2) ↔ ∀ a k, n ≠ 4 ^ a * (8 * k + 7) := by
  refine ⟨fun ⟨x, y, z, h⟩ a k h' ↦ four_pow_mul_ne_sq_add_sq_add_sq a k x y z (h' ▸ h), fun h ↦ ?_⟩
  induction n using Nat.strong_induction_on with | _ n ih
  rcases eq_or_ne n 0 with rfl | hn
  · exact ⟨0, 0, 0, rfl⟩
  by_cases h4 : 4 ∣ n
  · obtain ⟨n, rfl⟩ := h4
    obtain ⟨x, y, z, h⟩ := ih n (by omega) fun a k hk ↦ h (a + 1) k (by rw [hk]; ring)
    exact ⟨2 * x, 2 * y, 2 * z, by rw [h]; ring⟩
  obtain ⟨r, s, rfl, hr⟩ := sq_mul_squarefree n
  obtain ⟨t, rfl | rfl⟩ := even_or_odd' s
  · exact absurd ⟨t ^ 2 * r, by ring⟩ h4
  obtain ⟨x, y, z, h'⟩ := eq_sq_add_sq_add_sq_of_squarefree hr fun h7 ↦
    h 0 ((2 * t + 1) ^ 2 * r / 8) <| by
      obtain ⟨u, hu⟩ := even_mul_succ_self t
      have : (2 * t + 1) ^ 2 * r % 8 = 7 := by
        rw [mul_mod, show (2 * t + 1) ^ 2 = 8 * u + 1 by linarith, h7]; omega
      omega
  exact ⟨(2 * t + 1) * x, (2 * t + 1) * y, (2 * t + 1) * z, by rw [h']; ring⟩
