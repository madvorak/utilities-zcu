import Mathlib

lemma one_le_four {α : Type*} [AddCommMonoidWithOne α] [Preorder α] [ZeroLEOneClass α] [AddLeftMono α] :
    (1 : α) ≤ (4 : α) :=
  calc (1 : α)
    = 1 + 0 := (add_zero 1).symm
  _ ≤ 1 + 3 := add_le_add_right zero_le_three 1
  _ = 4     := by norm_num

lemma Nat.real_one_div_succ_pos (n : ℕ) : (1 : ℝ) / (n + 1) > 0 := by
  positivity

lemma ne_zero_of_ge_one {α : Type*} [Zero α] [One α] [PartialOrder α] [ZeroLEOneClass α] [NeZero (1 : α)]
    {x : α} (h1x : 1 ≤ x) : x ≠ 0 := by
  intro hx0
  rw [hx0] at h1x
  exact one_ne_zero (le_antisymm h1x zero_le_one)

lemma posPart_sub_posPart_sq_le (x y : ℝ) : (x⁺ - y⁺) ^ 2 ≤ (x - y) ^ 2 := by
  cases le_total x 0 <;>
  cases le_total y 0 <;>
  simp [*] <;>
  nlinarith

open scoped ENNReal
/-- The symbol `↱` converts a nonnegative real number to a nonzero `ℝ≥0∞` term, and a negative real number to zero. -/
scoped[ENNReal] prefix:max "↱" => ENNReal.ofReal

lemma natCast_div_natCast_eq_ofReal (p : ℕ) {q : ℕ} (hq : q ≠ 0) :
    (p : ℝ≥0∞) / (q : ℝ≥0∞) = ↱((p : ℝ) / (q : ℝ)) := by
  rw [ENNReal.ofReal_div_of_pos]
  · rw [ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
  · positivity

lemma ofReal_div_ofReal_toReal {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    (↱p / ↱q).toReal = p / q := by
  rw [ENNReal.toReal_div, ENNReal.toReal_ofReal hp, ENNReal.toReal_ofReal hq]

lemma rpow_le_ofReal_rpow_of_le_ofReal
    {α R : ℝ} (hα : 0 ≤ α) (hR : 0 < R)
    {x : ℝ≥0∞} (hx : x ≤ ↱R) :
    x ^ α ≤ ↱(R ^ α) := by
  convert ENNReal.rpow_le_rpow hx hα using 1
  rw [ENNReal.ofReal_rpow_of_pos hR]

lemma pow_transfer_ennreal_ofReal
    {a : ℝ} (ha : 0 ≤ a)
    {b : ℝ} (hb : 0 ≤ b)
    {c : ℝ} (hc : 0 < c)
    {d : ℝ} (hd : 0 < d)
    {r : ℝ} (hr : 0 ≤ r)
    (hcarb : c * a ^ r < b) :
    ↱a ^ (d * r) ≤ ↱(c ^ (-d)) * ↱b ^ d := by
  have har : 0 ≤ a ^ r :=
    Real.rpow_nonneg ha r
  have hcd : 0 ≤ c ^ (-d) :=
    (Real.rpow_pos_of_pos hc (-d)).le
  have hadr : a ^ (d * r) ≤ c ^ (-d) * b ^ d := by
    rw [mul_comm,
        Real.rpow_mul ha,
        Real.rpow_neg hc.le,
        ←div_eq_inv_mul,
        le_div_iff₀ (Real.rpow_pos_of_pos hc d),
        ←Real.mul_rpow har hc.le]
    rw [←mul_nonneg_iff_of_pos_right hc] at har
    exact Real.rpow_le_rpow har ((mul_comm c (a ^ r) ▸ hcarb).le) hd.le
  convert ENNReal.ofReal_le_ofReal hadr using 1
  · apply ENNReal.ofReal_rpow_of_nonneg ha
    nlinarith
  · convert ENNReal.ofReal_mul hcd using 2
    rotate_left
    exact ENNReal.ofReal_mul hcd
    norm_num [ENNReal.ofReal_mul (Real.rpow_nonneg hc.le _), ENNReal.ofReal_rpow_of_nonneg hb hd.le]

/-- Writing `↓t` is slightly more general than writing `Function.const _ t`. -/
notation:max "↓"t:arg => (fun _ => t)

/-- The left-to-right direction of `↔`. -/
postfix:max ".→" => Iff.mp

/-- The right-to-left direction of `↔`. -/
postfix:max ".←" => Iff.mpr

/-- `ℝ^n` is the `n`-dimensional Euclidean space. -/
notation:max "ℝ^"n:max => EuclideanSpace ℝ (Fin n)

open scoped RealInnerProductSpace

lemma inner_eq_mul (a b : ℝ) : ⟪a, b⟫ = a * b := by
  rw [RCLike.inner_apply']
  norm_num

open MeasureTheory

lemma eLpNorm_norm_rpow_div_eq
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {D : Type*} [NormedAddCommGroup D] (u : Ω → D)
    {p α : ℝ} (hα : 0 < α) (hp : 0 < p) :
    eLpNorm (‖u ·‖ ^ α) ↱(p / α) μ = (eLpNorm u ↱p μ) ^ α := by
  simp only [eLpNorm_norm_rpow, hα]
  rw [←ENNReal.ofReal_mul, div_mul_cancel₀ _ hα.ne']
  positivity

lemma integrable_norm_rpow_of_memLp
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {E : Type*} [NormedAddCommGroup E]
    {p : ℝ} (hp : 1 < p)
    {u : Ω → E} (hup : MemLp u ↱p μ) :
    Integrable (‖u ·‖ ^ p) μ := by
  convert hup.integrable_norm_rpow (ne_of_gt (ENNReal.ofReal_pos.← (zero_lt_one.trans hp)))
  simp [ENNReal.toReal_ofReal (zero_le_one.trans hp.le)]

lemma memLp_norm_rpow_div_of_memLp
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {E : Type*} [NormedAddCommGroup E]
    {α : ℝ} (hα : 0 < α)
    {u : Ω → E} {p : ℝ} (hup : MemLp u ↱p μ) :
    MemLp (‖u ·‖ ^ α) ↱(p / α) μ := by
  convert hup.norm_rpow_div ↱α using 1
  · simp [ENNReal.toReal_ofReal hα.le]
  · rw [ENNReal.ofReal_div_of_pos hα]

lemma memLp_rpow_div_of_memLp_of_ae_nonneg
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {α : ℝ} (hα : 0 < α)
    {v : Ω → ℝ} (h0v : 0 ≤ᵐ[μ] v) {p : ℝ} (hvp : MemLp v ↱p μ) :
    MemLp (v · ^ α) ↱(p / α) μ := by
  apply (memLp_norm_rpow_div_of_memLp hα hvp).ae_eq
  filter_upwards [h0v] with ω hω
  rw [Real.norm_of_nonneg hω]

lemma Real.HolderConjugate.integrable_memLp_mul_memLp
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {p q : ℝ} (hpq : Real.HolderConjugate p q)
    {g : Ω → ℝ} (hgq : MemLp g ↱q μ)
    {l : Ω → ℝ} (hlp : MemLp l ↱p μ) :
    Integrable (fun ω : Ω => g ω * l ω) μ := by
  convert hgq.integrable_mul hlp
  · rfl
  exact hpq.symm.ennrealOfReal

lemma Real.HolderConjugate.integrable_memLp_inner_memLp
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {p q : ℝ} (hpq : Real.HolderConjugate p q)
    {g : Ω → E} (hgq : MemLp g ↱q μ)
    {l : Ω → E} (hlp : MemLp l ↱p μ) :
    Integrable (fun ω : Ω => ⟪g ω, l ω⟫) μ := by
  apply (hpq.integrable_memLp_mul_memLp hgq.norm hlp.norm).mono' (hgq.left.inner hlp.left)
  filter_upwards with ω
  rw [Real.norm_eq_abs]
  exact abs_real_inner_le_norm (g ω) (l ω)

noncomputable def normSMulSelf {T : Type*} {n : ℕ} (_ : T) (ξ : ℝ^n) : ℝ^n := ‖ξ‖ • ξ
#eval 2
