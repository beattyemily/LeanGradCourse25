import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.Baire.CompleteMetrizable

open Set Topology Filter Classical Real

open scoped Filter

section Filters

#print Filter

variable {α β : Type*}

-- If `a : α`, the set of sets containing `a` is a filter
-- **ToDo**
example (a : α) : Filter α where
  sets := {A | a ∈ A}
  univ_sets := mem_univ a
  sets_of_superset := by
    intro S T hS hT
    apply hT.trans
    · rfl
    · exact hS
  inter_sets := by
    intro S T hS hT
    exact ⟨hS, hT⟩


-- `⌘`


-- the `atTop` filter
-- **ToDo**
example : Filter ℕ where
  sets := {A | ∃ n : ℕ, ∀ a : ℕ, n ≤ a → a ∈ A}
  univ_sets := by
    use 0
    intro a
    tauto
  sets_of_superset := by
    intro F G hF hFG
    obtain ⟨n, hn⟩ := hF
    use n
    intro a ha
    apply hFG.trans (by rfl)
    exact hn a ha
  inter_sets := by
    intro S T ⟨n, hn⟩ ⟨m, hm⟩
    use max n m
    intro a ha
    simp only [sup_le_iff] at ha
    exact ⟨hn a ha.1, hm a ha.2⟩

#print Filter.atTop
#check atTop
#print Filter.mem_atTop


-- The neighbourhoods of a point in `ℝ`
-- **ToDo**
example (a : ℝ) : Filter ℝ where
  sets := {A | ∃ ε > 0, Set.Ioo (a - ε) (a + ε) ⊆ A}
  univ_sets := by
    use 1, zero_lt_one, subset_univ _
  sets_of_superset h h' := by
    obtain ⟨ε, hpos, h⟩ := h
    use ε, hpos, subset_trans h h'
  inter_sets h h' := by
    obtain ⟨ε, hpos, h⟩ := h
    obtain ⟨ε', hpos', h'⟩ := h'
    use min ε ε', lt_min_iff.mpr ⟨hpos, hpos'⟩
    intro z hz
    apply (inter_subset_inter h h')
    rw [Ioo_inter_Ioo]
    change z ∈ Ioo (max (a - ε) (a - ε')) (min (a + ε) (a + ε'))
    rw [max_sub_sub_left a ε ε', min_add_add_left a ε ε']
    exact hz



-- # § Exercises


-- More generally, if `s : Set α`, the set of sets containing `s` is a filter.
-- **Exercise**
example (s : Set α) : Filter α where
  sets := {A : Set α | s ⊆ A}
  univ_sets := subset_univ s
  sets_of_superset h h' := subset_trans h h'
  inter_sets h h' := subset_inter h h'


-- Many results about `𝓟` have names containing `principal`.

-- **Exercise**
example (s t : Set α) : t ∈ 𝓟 s ↔ s ⊆ t := mem_principal

-- **Exercise**
example (s t X : Set α) (hst : t ⊆ s) : X ∈ 𝓟 s → X ∈ 𝓟 t := by
  intro h
  rw [mem_principal] at h ⊢
  exact hst.trans h


-- Define the `atBot` filter: it can be easier to use the definition `Set.Ici a = [a, + ∞)`.
-- **Exercise**
example : Filter ℕ where
  sets := {A | ∃ n, Set.Ici n ⊆ A}
  univ_sets := by
    use 0, subset_univ _
  sets_of_superset h h' := by
    obtain ⟨n, hn⟩ := h
    use n, fun _ hx ↦ (subset_trans hn h') hx
  inter_sets h h' := by
    obtain ⟨n, hn⟩ := h
    obtain ⟨m, hm⟩ := h'
    use max n m
    erw [← Ici_inter_Ici]
    exact fun _ hx ↦ (inter_subset_inter hn hm) hx



/- If `a : ℝ`, we can also look at the set of subsets of `ℝ` that contain an interval `(a-ε,a]`
with `ε > 0`, and this is still a filter. This open-closed interval `(a -ε, a]` is called
`Set.Ioc (a - ε) a`.
**Exercise** -/
def nhds_left (a : ℝ) : Filter ℝ where
  sets := {A | ∃ ε > 0, Ioc (a - ε) a ⊆ A}
  univ_sets := by
    use 1, zero_lt_one, subset_univ _
  sets_of_superset h h' := by
    obtain ⟨ε, hpos, h⟩ := h
    use ε, hpos, subset_trans h h'
  inter_sets h h' := by
    obtain ⟨ε, hpos, h⟩ := h
    obtain ⟨ε', hpos', h'⟩ := h'
    use min ε ε', lt_min_iff.mpr ⟨hpos, hpos'⟩
    intro z hz
    apply (inter_subset_inter h h')
    rw [Ioc_inter_Ioc]
    change z ∈ Ioc (max (a - ε) (a - ε')) (min a a)
    rw [max_sub_sub_left a ε ε', min_self]
    exact hz


-- `⌘`


-- ## Convergence: Take 1


-- **ToDo**
def Tendsto_preimage (f : α → β) (F : Filter α) (G : Filter β) : Prop :=
  ∀ V ∈ G, f ⁻¹' V ∈ F

-- The behaviour of preimages through composition of functions
#check Set.preimage_comp

-- Compatibility with composition.
-- **ToDo**
example {γ : Type*} (f : α → β) (g : β → γ) (F : Filter α) (G : Filter β) (H : Filter γ) :
    Tendsto_preimage f F G → Tendsto_preimage g G H → Tendsto_preimage (g ∘ f) F H := by
  intro h h' U hU
  rw [preimage_comp]
  apply h
  apply h'
  exact hU



-- Link with the "classical" notion
-- **ToDo**
example (f : ℝ → ℝ) (a b : ℝ) : Tendsto_preimage f (𝓝 a) (𝓝 b) ↔
    ∀ ε > 0, ∃ δ > 0, ∀ x, x ∈ Ioo (a - δ) (a + δ) →
    f x ∈ Ioo (b - ε) (b + ε) := by
  constructor
  · intro H ε ε_pos
    -- rw [Tendsto_preimage] at H
    have hVb : Ioo (b - ε) (b + ε) ∈ 𝓝 b := by
      apply Ioo_mem_nhds <;> linarith
    specialize H _ hVb
    rw [Metric.mem_nhds_iff] at H
    obtain ⟨δ, δ_pos, h_incl⟩ := H
    refine ⟨δ, δ_pos, ?_⟩
    simp only [Ioo_eq_ball, sub_add_add_cancel, add_self_div_two, add_sub_sub_cancel] at h_incl ⊢
    apply h_incl
  · intro H
    -- rw [Tendsto_preimage]
    intro V hV
    rw [Metric.mem_nhds_iff] at hV ⊢
    obtain ⟨ε, ε_pos, hε⟩ := hV
    obtain ⟨δ, δ_pos, h_incl⟩ := H ε ε_pos
    simp only [Ioo_eq_ball, sub_add_add_cancel, add_self_div_two, add_sub_sub_cancel] at h_incl
    refine ⟨δ, δ_pos, ?_⟩
    rw [← image_subset_iff]
    apply subset_trans _ hε
    rw [image_subset_iff]
    exact h_incl

-- **Exercise**
example (u : ℕ → ℝ) (x₀ : ℝ) : Tendsto_preimage u atTop (𝓝 x₀) ↔
    ∀ ε > 0, ∃ N, ∀ n ≥ N, u n ∈ Ioo (x₀ - ε) (x₀ + ε) := by
  constructor
  · intro H ε ε_pos
    have hVb : Ioo (x₀ - ε) (x₀ + ε) ∈ 𝓝 x₀ := by
      apply Ioo_mem_nhds <;> linarith
    specialize H _ hVb
    rwa [mem_atTop_sets] at H
  · intro H
    intro V hV
    rw [mem_atTop_sets]
    rw [Metric.mem_nhds_iff] at hV
    obtain ⟨ε, ε_pos, hε⟩ := hV
    obtain ⟨N, hN⟩ := H ε ε_pos
    use N
    simp only [Ioo_eq_ball, sub_add_add_cancel, add_self_div_two, add_sub_sub_cancel] at hN
    exact fun n hn ↦ hε <| hN n hn



-- `⌘`



-- ## Convergence: Take 2


-- The order on filters generalises the one on sets
-- **ToDo**
example (s t : Set α) : s ⊆ t ↔ (𝓟 t).sets ⊆ (𝓟 s).sets := by
  constructor
  · exact fun h _ hA ↦ le_trans h hA
  · exact fun h ↦ h (mem_principal_self t)


-- **Exercise**
example (F : Filter α) (s : Set α) : 𝓟 s ≤ F ↔ ∀ A ∈ F, s ⊆ A := by
  constructor
  · exact fun h _ hA ↦ h hA
  · exact fun h A hA ↦ h A hA


-- **Exercise**
example (F : Filter α) (s : Set α) : F ≤ 𝓟 s ↔ s ∈ F := by
  constructor
  · exact fun h ↦ h (mem_principal_self s)
  · exact fun h _ hA ↦ F.sets_of_superset h hA


#print Filter.map

-- This is compatible to the definition for sets.
-- **ToDo**
example {s : Set α} (f : α → β) : (𝓟 s).map f = 𝓟 (f '' s) := by
  ext A
  change f ⁻¹'A ∈ 𝓟 s ↔ A ∈ 𝓟 (f '' s)
  rw [mem_principal, mem_principal]
  exact Set.image_subset_iff.symm


/- Now to prove the compatibility of limits with compositions,
we use the properties of `Filter.map`.-/
#print Filter.map_mono -- `Filter.map f` is monotone.
-- If F ≤ F', then map f F ≤ map f F'.
#print Filter.map_map -- `Filter.map (g ∘ f) = Filter.map g ∘ Filter.map f`
-- **???**
example {X Y Z : Type*} (f : X → Y) (g : Y → Z) (F : Filter X)
    (G : Filter Y) (H : Filter Z) :
    Tendsto f F G → Tendsto g G H → Tendsto (g ∘ f) F H := by
  intro h h'
  change map (g ∘ f) F ≤ H
  rw [← map_map]
  refine le_trans ?_ h'
  apply map_mono
  exact h


#print Tendsto_preimage
#print Tendsto

-- **Exercise**
example {X Y : Type*} (f : X → Y) (F : Filter X) (G : Filter Y) :
    Tendsto f F G ↔ Tendsto_preimage f F G := Iff.rfl


-- The squeeze theorem
-- **Exercise**
example (f g h : ℝ → ℝ) (a x : ℝ) (hf : atTop.map f ≤ 𝓝 a)
    (hg : atTop.map g ≤ 𝓝 x) (hh : atTop.map h ≤ 𝓝 a) (Hfg : f ≤ g) (Hgh : g ≤ h) : x = a := by
  have : 𝓝 a = 𝓝 x := by
    apply eq_of_le_of_le
    have : (atTop.map h).map f ≤ (𝓝 a).map f := by
      apply Filter.map_mono hh
    have : (𝓝 a).map f ≤ (𝓝 a).map g := by
      have := @Filter.pi_le_pi
    -- have : Monotone (λ f : ℝ → ℝ ↦ Filter.map f) := by
      -- have := @Filter.bind_mono (f₁ := 𝓝 a) (f₂ := 𝓝 a) (β := ℝ) (g₁ := fun x ↦ (𝓝 x).map g)
    -- apply map_mono
    -- have := @Filter.map_mono (m := f)
    -- have := Filter.map




-- `⌘`



-- ## END OF FILTERS FOR LIMITS


-- # Second part on filters
/- Another use of filters is that they give a convenient
way to talk about properties that are true for `x` big enough,
for `x` close enough to a fixed point, for almost all `x` etc.

For this, we use the function `Filter.Eventually`. If
`p : α → Prop` and `F : Filter α`, then `Filter.Eventually p F`
(or `F.Eventually p`)
means that `{x | p x}` is an element of `F`. Intuitively, this
means that `p` is true on the "set" corresponding to `F`.

The notation for this is:
`∀ᶠ x in F, p x`. (\ + forall + \ + ^f)
-/

example : ∀ᶠ n in atTop (α := ℕ), 2 ≤ n := by
  dsimp [Filter.Eventually]
  simp
  use 2
  simp

example : ∀ᶠ x in nhds (0 : ℝ), |x| ≤ 1/2 := by
  dsimp [Filter.Eventually]
  rw [(nhds_basis_Ioo_pos 0).mem_iff]
  use 1/2
  constructor
  · simp only [one_div, inv_pos, Nat.ofNat_pos]
  · simp only [zero_sub, zero_add]
    intro x ⟨hx₁, hx₂⟩
    rw [mem_setOf_eq, abs_le]
    exact ⟨le_of_lt hx₁, le_of_lt hx₂⟩

/- Now let's see what the properties of a filter say about `∀ᶠ`:

(1) `⊤ ∈ F` means that: `∀ x, p x → ∀ᶠ x in F, p x`.-/
#check Eventually.of_forall

/-(2) The stability of `F` by taking a superset means that, if
`q : α → Prop` is another function, and if
`∀ᶠ x, p x` and `∀ x, p x → q x`, then `∀ᶠ x, q x`.-/
#check Eventually.mono

/-(3) The stability of `F` by intersections means that, if
`∀ᶠ x in F, p x` and `∀ᶠ x in F, q x`, then
`∀ᶠ x in F, p x ∧ q x`.-/
#check Filter.Eventually.and

example (P Q : ℕ → Prop) (hP : ∀ᶠ n in atTop, P n) (hQ : ∀ᶠ n in atTop, Q n) :
    ∀ᶠ n in atTop, P n ∧ Q n := by
  dsimp [Filter.Eventually] at hP hQ ⊢
  exact atTop.inter_sets hP hQ

/- There are two special cases of `Filter.Eventually` for equalities
and inequalities:-/
#print Filter.EventuallyEq
#print Filter.EventuallyLE


/- They have special notation too:-/
example (u v : ℕ → ℝ) : (∀ᶠ n in atTop, u n = v n) ↔ u =ᶠ[atTop] v := Iff.refl _

example (u v : ℕ → ℝ) : (∀ᶠ n in atTop, u n ≤ v n) ↔ u ≤ᶠ[atTop] v := Iff.refl _

-- For example, two sequences that are eventually equal
-- for the filter `atTop` have the same limit.
example (u v : ℕ → ℝ) (h : u =ᶠ[atTop] v) (x₀ : ℝ) :
    Tendsto u atTop (𝓝 x₀) ↔ Tendsto v atTop (𝓝 x₀) :=
  tendsto_congr' h

/- There is a tactic called `filter_upwards` to deal with goals
of the `∀ᶠ s in F, ...`.-/

/-- From the documentation:
`filter_upwards [h₁, ⋯, hₙ]` replaces a goal of the form `s ∈ f` and terms
`h₁ : t₁ ∈ f, ⋯, hₙ : tₙ ∈ f` with `∀ x, x ∈ t₁ → ⋯ → x ∈ tₙ → x ∈ s`.
The list is an optional parameter, `[]` being its default value.

`filter_upwards [h₁, ⋯, hₙ] with a₁ a₂ ⋯ aₖ` is a short form for
`{ filter_upwards [h₁, ⋯, hₙ], intros a₁ a₂ ⋯ aₖ }`.

`filter_upwards [h₁, ⋯, hₙ] using e` is a short form for
`{ filter_upwards [h1, ⋯, hn], exact e }`.

Combining both shortcuts is done by writing
`filter_upwards [h₁, ⋯, hₙ] with a₁ a₂ ⋯ aₖ using e`.
Note that in this case, the `aᵢ` terms can be used in `e`.
-/

-- Without `filter_upwards`.
example (P Q R : ℕ → Prop) (hP : ∀ᶠ n in atTop, P n) (hQ : ∀ᶠ n in atTop, Q n)
    (hR : ∀ᶠ n in atTop, P n ∧ Q n → R n) : ∀ᶠ n in atTop, R n := by
  have := hP.and (hQ.and hR)
  apply Eventually.mono this
  rintro n ⟨h, h', h''⟩
  exact h'' ⟨h, h'⟩

example (P Q R : ℕ → Prop) (hP : ∀ᶠ n in atTop, P n) (hQ : ∀ᶠ n in atTop, Q n)
    (hR : ∀ᶠ n in atTop, P n ∧ Q n → R n) : ∀ᶠ n in atTop, R n := by
  filter_upwards [hP, hQ, hR] with n h h' h'' using h'' ⟨h, h'⟩

-- An exercise: if the sequence `u` converges to `x` and
-- `u n` is in `M` for `n` big enough, then `x` is in the closure
-- of `M`.

example (u : ℕ → ℝ) (M : Set ℝ) (x : ℝ) (hux : Tendsto u atTop (𝓝 x))
    (huM : ∀ᶠ n in atTop, u n ∈ M) : x ∈ closure M := by
  rw [mem_closure_iff_clusterPt]
  change (𝓝 x ⊓ 𝓟 M).NeBot
  apply neBot_of_le (f := map u atTop)
  rw [le_inf_iff]
  refine ⟨hux, ?_⟩
  refine le_trans (map_mono (m := u) (le_principal_iff.mpr huM)) ?_
  simp only [map_principal, le_principal_iff, mem_principal, image_subset_iff]
  intro x
  simp

--Useful lemmas for the exercise:
#check mem_closure_iff_clusterPt
#print ClusterPt -- note that `ClusterPt x F` means by definition
                 -- that `𝓝 x ⊓ F` is not the `⊥` filter
#check le_principal_iff
#check neBot_of_le

/- Another filter notion is `Filter.Frequently`. You
would use it for example to express something like
"there exist arbitrarily large `n` in `ℕ` such that so and so".-/

#print Filter.Frequently
-- `Filter.Frequently p F` means `¬∀ᶠ (x : α) in f, ¬p x` i.e.
-- `{x | ¬p x} ∉ F`. It is written `∃ᶠ x in F, p x`.
-- This is actually equivalent to saying that, for every `A ∈ F`,
-- there exists `x ∈ A` such that `p x`. Don't believe me?

example (p : α → Prop) (F : Filter α) :
    (∃ᶠ x in F, p x) ↔ ∀ A ∈ F, ∃ x ∈ A, p x := by
  constructor
  · intro h A hA
    by_contra habs
    push_neg at habs
    have hsub : A ⊆ {x | ¬p x} := by
      intro x hx
      simp only [mem_setOf_eq, habs x hx, not_false_eq_true]
    have := F.mem_of_superset hA hsub
    exact h this
  · dsimp [Filter.Frequently]
    intro h habs
    obtain ⟨x, hx₁, hx₂⟩ := h _ habs
    simp only [mem_setOf_eq] at hx₁
    exact hx₁ hx₂

-- Of course, this result is already in mathlib:
#check Filter.frequently_iff

example : ∃ᶠ n in atTop (α := ℕ), Nat.Prime n := by
  rw [frequently_atTop]
  intro a
  obtain ⟨p, hp₁, hp₂⟩ := Nat.exists_infinite_primes a
  use p



end Filters

section Limits

-- ## From Xavier, Calculus1, ll 93-207

/-
  # Limits computation
-/

-- Some classical limits
example : Tendsto (fun n : ℕ ↦ 1 / (n : ℝ)) atTop (𝓝 0) := by
  exact tendsto_const_div_atTop_nhds_zero_nat 1

example : Tendsto (fun n : ℕ ↦ 1 / n) atTop (𝓝 0) := by
  refine Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [eventually_gt_atTop 1] with n hn
  rw [eq_comm, Nat.div_eq_zero_iff]
  exact Or.inr hn

example : Tendsto (fun n : ℕ ↦ n) atTop atTop := by
  exact tendsto_natCast_atTop_atTop -- This is a bit cheating

#check Tendsto.congr'

#check Filter.eventually_ne_atTop

example : Tendsto (fun n : ℕ ↦ (n + 1 : ℝ) / n) atTop (𝓝 1) := by
  have h1 := tendsto_const_div_atTop_nhds_zero_nat 1
  have h2 : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have h3 := Tendsto.add h1 h2
  rw [zero_add] at h3
  refine Tendsto.congr' ?_ h3
  rw [Filter.EventuallyEq]
  filter_upwards [eventually_ne_atTop 0] with n hn
  rw [add_div, div_self]
  · ring
  · rwa [Nat.cast_ne_zero]

theorem lemma1 : Tendsto (fun n : ℕ ↦ n ^ 2) atTop atTop := by
  rw [tendsto_pow_atTop_iff]
  exact two_ne_zero

theorem lemma2 : Tendsto (fun n : ℕ ↦ n ^ 2 + n) atTop atTop := by
  refine tendsto_atTop_add ?_ ?_
  exact lemma1
  exact tendsto_natCast_atTop_atTop

-- Squeeze theorem
#check tendsto_of_tendsto_of_tendsto_of_le_of_le

#check tendsto_of_tendsto_of_tendsto_of_le_of_le'

example : Tendsto (fun n : ℕ ↦ ((n : ℝ) ^ 2 + 4 * Real.sqrt n) / (n ^ 2)) atTop (𝓝 1) := by
  have l1 : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have l2 : Tendsto  (fun n : ℕ ↦ ((n : ℝ) ^ 2 + n) / (n ^ 2)) atTop (𝓝 1) := by
    have l3 : Tendsto (fun n : ℕ ↦ 1 / (n : ℝ)) atTop (𝓝 0) := tendsto_const_div_atTop_nhds_zero_nat 1
    have l4 := Tendsto.add l1 l3
    rw [add_zero] at l4
    refine Tendsto.congr' ?_ l4
    filter_upwards [eventually_ne_atTop 0] with n hn
    field_simp
    ring
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' l1 l2 ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with n hn
    rw [one_le_div₀, le_add_iff_nonneg_right]
    · positivity
    · positivity
  · filter_upwards [eventually_ge_atTop 16] with n hn
    rw [div_le_div_iff_of_pos_right, add_le_add_iff_left]
    · suffices 4 ≤ √ n by
        convert mul_le_mul_of_nonneg_right this (Real.sqrt_nonneg n)
        rw [mul_self_sqrt]
        exact Nat.cast_nonneg n
      rw [Real.le_sqrt]
      · rwa [show (4 : ℝ) ^ 2 = (16 : ℕ) by norm_num, Nat.cast_le]
      · positivity
      · exact Nat.cast_nonneg n
    positivity

example (f : ℝ → ℝ) (g : ℝ → ℝ) (a l : ℝ) (hf : Tendsto f (𝓝 a) (𝓝 l)) (h : f = g) :
    Tendsto g (𝓝 a) (𝓝 l) := by
  exact Tendsto.congr (congrFun h) hf

-- Congruence for limits
example (f : ℝ → ℝ) (g : ℝ → ℝ) (a l : ℝ) (hf : Tendsto f (𝓝 a) (𝓝 l)) (h : f =ᶠ[𝓝 a] g) :
    Tendsto g (𝓝 a) (𝓝 l) := by
  exact (tendsto_congr' h).mp hf

-- Unicity of limits
example (f : ℝ → ℝ) (a l l' : ℝ) (hf : Tendsto f (𝓝 a) (𝓝 l))  (hf' : Tendsto f (𝓝 a) (𝓝 l')) :
    l = l' := by
  exact tendsto_nhds_unique hf hf'

-- L'Hôpital's rule
example : Tendsto (fun x ↦ (exp x - 1) / (sin x)) (𝓝[≠] 0) (𝓝 1) := by
  refine deriv.lhopital_zero_nhds ?_ ?_ ?_ ?_ ?_
  · filter_upwards with x
    refine DifferentiableAt.sub ?_ ?_
    · exact differentiableAt_exp
    · exact differentiableAt_const 1
  · refine ContinuousAt.eventually_ne ?_ ?_
    · rw [Real.deriv_sin]
      refine Continuous.continuousAt ?_
      exact continuous_cos
    · rw [Real.deriv_sin, cos_zero]
      exact one_ne_zero
  · convert Tendsto.sub (continuous_exp.tendsto 0) (tendsto_const_nhds (x := 1))
    rw [exp_zero, sub_self]
  · convert continuous_sin.tendsto 0
    rw [sin_zero]
  · suffices Tendsto (fun x ↦ exp x / cos x) (𝓝 0) (𝓝 1) by
      refine Tendsto.congr ?_ this
      intro x
      rw [Real.deriv_sin, deriv_sub, Real.deriv_exp, deriv_const, sub_zero]
      · exact differentiableAt_exp
      · exact differentiableAt_const 1
    have c1 : ContinuousAt rexp 0 := Continuous.continuousAt continuous_exp
    have c2 : ContinuousAt cos 0 := Continuous.continuousAt continuous_cos
    convert (ContinuousAt.div c1 c2 ?_).tendsto using 2
    · simp
    · simp

open Asymptotics in
lemma result1 (a : ℕ → ℝ) (h2 : a ~[atTop] fun n ↦ n) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, (1 - ε) * n < a n ∧ a n < (1 + ε) * n := by
  rw [Asymptotics.isEquivalent_iff_tendsto_one] at h2
  · rw [Metric.tendsto_nhds] at h2
    simp_rw [dist_eq_norm, Real.norm_eq_abs] at h2
    specialize h2 ε hε
    filter_upwards [h2, eventually_gt_atTop 0] with n hn hn'
    rw [abs_lt] at hn
    constructor
    · replace hn := hn.1
      dsimp at hn
      rwa [lt_sub_iff_add_lt', ← sub_eq_add_neg, lt_div_iff₀] at hn
      rwa [Nat.cast_pos]
    · replace hn := hn.2
      dsimp at hn
      rwa [sub_lt_iff_lt_add', div_lt_iff₀] at hn
      rwa [Nat.cast_pos]
  · filter_upwards [eventually_ne_atTop 0] with n hn
    rwa [Nat.cast_ne_zero]


example (x : ℝ) :
    cos x = ∑' (n : ℕ), (-1 : ℝ) ^ n * x ^ (2 * n) /(2 * n).factorial := by
  exact cos_eq_tsum x

example : ∑' (n : ℕ), (n : ℝ) = 0 := by
  refine tsum_eq_zero_of_not_summable ?_
  by_contra h
  replace h := Summable.tendsto_atTop_zero h
  rw [NormedAddCommGroup.tendsto_nhds_zero] at h
  specialize h 1 zero_lt_one
  rw [eventually_atTop] at h
  obtain ⟨N, hN⟩ := h
  specialize hN (N + 1) (Nat.le_add_right N 1)
  rw [Real.norm_eq_abs, Nat.cast_add_one, abs_of_pos (by positivity)] at hN
  linarith

end Limits
