import Mathlib.GroupTheory.Subgroup.Center


open Function Set
-- Observe how it understands automatically what `1` and `*` are
-- @[to_additive]
example (M : Type*) [Monoid M] (a b c : M) (hba : b * a = 1) (hac : a * c = 1) : b = c := by
  rw [← one_mul c]
  rw [← hba]
  rw [mul_assoc]
  rw [hac]
  rw [mul_one b]


example (M N : Type*) [Monoid M] [Monoid N] (f : M →* N) : f 1 = 1 := by
  apply map_one

example (M N : Type*) [Monoid M] [CommMonoid N] (f : M →* N) (m₁ m₂ : M) (n : N) (h : f m₁ * n = 1) :
  f (m₁ * m₂) * n = f m₂ := by
  rw [map_mul]
  rw [mul_comm (f m₁) _]
  rw [mul_assoc]
  rw [h]
  rw [mul_one]

-- two simultaneous structures!
example (M N : Type*) [Monoid M] [CommMonoid N] (f : M →* N) (m₁ m₂ : M) (n : N) (h : f m₁ * n = 1) :
  f (m₁ * m₂) * n = f m₂ * n := by
  sorry

-- In general, `*`  and `+` are completely unrelated, so do not hope for this...
example (M : Type*) [Monoid M] [AddMonoid M] (a b : M) : a * 1 = a + 0 := by
  sorry

example {G : Type*} [Group G] (x y z : G) : x * (y * z) * (x * z)⁻¹ * (x * y * x⁻¹)⁻¹ = 1 := by
  group

example {A : Type*} [AddCommGroup A] (a b : A) : a + 0 + b + 0 = b + a := by abel

-- `⌘`

example (G H : Type*) [Group G] [Group H] (f : G →* H) (g : G) : f (g⁻¹) = (f g)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one]
  rw [← map_mul]
  rw [inv_mul_cancel]
  apply map_one --try with `exact`: it does not work!
  -- exact MonoidHom.map_inv f g

noncomputable --what's this?
def IsoOfBijective (G H : Type*) [Group G] [Group H] (f : G →* H)
    (h_surj : Surjective f) (h_inj : Injective f) : G ≃* H := by
  fconstructor -- the difference between `constructor` and `fconstructor`
  · apply Equiv.ofBijective
    rw [Bijective]
    exact ⟨h_inj, h_surj⟩
  · intro g h
    simp only [Equiv.toFun_as_coe, Equiv.ofBijective_apply, map_mul]

-- ##Subgroups

-- `ℤ` as a subgroup of `ℚ`
example : AddSubgroup ℚ where
  carrier := Set.range ((↑) : ℤ → ℚ)
  add_mem' := by
    rintro _ _ ⟨n, rfl⟩ ⟨m, rfl⟩
    use n + m
    simp
  zero_mem' := by
    use 0
    simp
  neg_mem' := by
    rintro _ ⟨n, rfl⟩
    use -n
    simp

def Stupid (G : Type*) [Group G] : Subgroup G where --show the `_`-trick
  carrier := univ
  mul_mem' := by
    intro a b ha hb
    exact mem_univ (a * b) -- trivial
  one_mem' := by
    simp only
    exact mem_univ 1
  inv_mem' := fun _ ↦ mem_univ _

example : Stupid = ⊤ := rfl

example (G H : Type*) [AddGroup G] [AddGroup H] (f : G →+ H) : AddSubgroup G where
  carrier := {g : G | f g = 0}
  add_mem' := by
    intro a b ha hb
    rw [Set.mem_setOf]
    rw [map_add]
    rw [hb]
    rw [ha]
    rw [zero_add]
  zero_mem' := by
    rw [Set.mem_setOf]
    apply map_zero
  neg_mem' := by
    intro x hx
    simp only
    rw [Set.mem_setOf]
    rw [map_neg]
    rw [hx]
    rw [neg_zero]

-- one more example, then some exercics and let's pass to rings

section Rings

end Rings
