import group_theory.quotient_group
import group_theory.subgroup.basic

variables {G : Type*} [group G]

def subgroup_generated_by (S : set G) : subgroup G := 
⨅ (H : subgroup G) (hH : S ⊆ H), H

include G
def foo : ℕ → ℕ := λ a, a

namespace subgroup_gen

inductive carrier (S : set G) : set G 
| of (s : G) (hs : s ∈ S) : carrier s
| one : carrier 1
| mul {x y : G} : carrier x → carrier y → carrier (x * y)
| inv {x : G} : carrier x → carrier x⁻¹

end subgroup_gen

open subgroup_gen

def subgroup_gen (S : set G) : subgroup G := 
{ carrier := carrier S,
  mul_mem' := λ a b ha hb, carrier.mul ha hb,
  one_mem' := carrier.one,
  inv_mem' := λ x hx, carrier.inv hx }

example (S : set G) : subgroup_generated_by S = subgroup_gen S :=
begin
  apply le_antisymm,
  { intros x hx, unfold subgroup_generated_by at hx,
    simp_rw subgroup.mem_infi at hx,
    apply hx,
    intros s hs,
    apply carrier.of,
    exact hs },
  { intros x hx, unfold subgroup_generated_by, 
    simp_rw subgroup.mem_infi, 
    intros H hH,
    induction hx,
    case carrier.of : s hs { apply hH, exact hs },
    case carrier.one { exact H.one_mem },
    case carrier.mul : a b h1 h2 hh1 hh2 { apply H.mul_mem, exact hh1, exact hh2 },
    case carrier.inv : a _ ha { apply H.inv_mem, exact ha } }
end

/-!
QUOTIENTS
-/

variable (R : G → G → Prop)

/-!

I want to construct the smallest relation `S : G → G → Prop` 
which satisfies the following properties:
1. It should be implied by `R`, meaning if `R a b` then `S a b` should also hold true.
2. `S` is an equivalence relation.
3. `G/S` is a group where the product has the form `[a] * [b] = [a * b]` and inversion
  has the form `[a]⁻¹ = [a⁻¹]`.
-/

inductive congr_rel (R : G → G → Prop) : G → G → Prop
| of (x y : G) (h : R x y) : congr_rel x y
| refl (x : G) : congr_rel x x
| symm (x y : G) : congr_rel x y → congr_rel y x
| trans (x y z : G) : congr_rel x y → congr_rel y z → congr_rel x z
| inv (x y : G) : congr_rel x y → congr_rel x⁻¹ y⁻¹ 
| mul (x x' y y' : G) : congr_rel x x' → congr_rel y y' → congr_rel (x * y) (x' * y')

def congr_setoid (R : G → G → Prop) : setoid G := 
{ r := congr_rel R,
  iseqv := begin
    refine ⟨_,_,_⟩,
    { apply congr_rel.refl, },
    { apply congr_rel.symm },
    { apply congr_rel.trans },
  end }

def quotient_group (R : G → G → Prop) := quotient (congr_setoid R)

instance : group (quotient_group R) :=
{ mul := λ a b, quotient.lift_on₂' a b (λ x y, quotient.mk' $ x * y) begin
    intros a₁ a₂ b₁ b₂ h1 h2,
    dsimp,
    apply quotient.sound',
    apply congr_rel.mul,
    exact h1,
    exact h2,
  end,
  mul_assoc := begin
    rintros ⟨a⟩ ⟨b⟩ ⟨c⟩,
    apply quotient.sound',
    rw mul_assoc,
    apply setoid.refl',
  end,
  one := quotient.mk' 1,
  one_mul := begin
    rintros ⟨a⟩,
    apply quotient.sound',
    rw one_mul,
    apply setoid.refl',
  end,
  mul_one := begin
    rintros ⟨a⟩,
    apply quotient.sound',
    rw mul_one,
    apply setoid.refl',
  end,
  inv := λ x, quotient.lift_on' x (λ g, quotient.mk' g⁻¹) begin
    intros a b h,
    dsimp,
    apply quotient.sound',
    apply congr_rel.inv,
    exact h,
  end,
  mul_left_inv := begin
    rintros ⟨a⟩,
    apply quotient.sound',
    rw mul_left_inv,
    apply setoid.refl',
  end }

def π : G →* quotient_group R := 
{ to_fun := quotient.mk',
  map_one' := rfl,
  map_mul' := λ a b, rfl }

def desc_to_quotient
  {H : Type*} [group H] 
  (f : G →* H)
  (hf : ∀ a b : G, R a b → f a = f b) :
  quotient_group R →* H :=
{ to_fun := λ x, quotient.lift_on' x f begin
    intros a b h,
    induction h,
    case congr_rel.of : a b h { apply hf, assumption },
    case congr_rel.refl { refl },
    case congr_rel.symm { symmetry, assumption },
    case congr_rel.trans { cc },
    case congr_rel.inv : a b h hh { simp_rw [f.map_inv, hh], },
    case congr_rel.mul : a a' b b' h hh h1 h2 { simp_rw [f.map_mul, h1, h2] }
  end,
  map_one' := f.map_one,
  map_mul' := begin
    rintros ⟨a⟩ ⟨b⟩,
    apply f.map_mul,
  end }

theorem universal_property_of_the_quotient_by_a_relation 
  {H : Type*} [group H] 
  (f : G →* H)
  (hf : ∀ a b : G, R a b → f a = f b) :
  ((desc_to_quotient R f hf).comp (π R) = f) ∧
  (∀ (g : quotient_group R →* H) (hg : g.comp (π R) = f), g = desc_to_quotient R f hf) := 
begin
  split,
  { ext, refl, },
  { intros g hg,
    ext ⟨t⟩,
    apply_fun (λ e, e t) at hg,
    exact hg }
end