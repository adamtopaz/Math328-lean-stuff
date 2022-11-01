import tactic
import group_theory.quotient_group

variable (α : Type*) -- "Let α be a set."
variables (R : setoid α)

-- The "usual" construction of a quotient of α by R.
def Q : Type* :=
{ S : set α | ∃ x : α, S = { y : α | R.rel x y } }

def π : α → Q α R :=  
λ a : α, ⟨{ b | R.rel a b }, begin
  change ∃ t, _,
  refine ⟨a, _⟩,
  refl,
end⟩

theorem π_surjective : function.surjective (π α R) := 
begin
  change ∀ q : _, ∃ a : α, _,
  intros q,
  obtain ⟨S, a, ha⟩ := q,
  use a,
  unfold π,
  apply subtype.ext,
  change {b : α | R.rel a b} = S,
  symmetry,
  assumption,
end

noncomputable def desc_to_Q 
  (β : Type*) 
  (f : α → β)
  (hf : ∀ a b : α, R.rel a b → f a = f b) :
  Q α R → β := 
λ q, f q.2.some

lemma desc_to_Q_spec
  (β : Type*) 
  (f : α → β)
  (hf : ∀ a b : α, R.rel a b → f a = f b) 
  (a : α) 
  (q : Q α R)
  (ha : π α R a = q) :
  desc_to_Q α R β f hf q = f a :=
begin
  let a' : α := q.2.some,
  have ha' : q.1 = { b : α | R.rel a' b } := q.2.some_spec,
  have : desc_to_Q α R β f hf q = f a' := rfl,
  rewrite [this], clear this,
  apply hf,
  rewrite [← ha] at ha',
  unfold π at ha',
  change {b : α | R.rel a b} = _ at ha',
  suffices : a ∈ { b : α | R.rel a' b },
  { exact this },
  rewrite [← ha'],
  apply setoid.refl,
end

theorem universal_property_of_Q 
  (β : Type*) 
  (f : α → β)
  (hf : ∀ a b : α, R.rel a b → f a = f b) :
  (desc_to_Q α R β f hf) ∘ π α R = f ∧ 
  ∀ (h : Q α R → β), h ∘ π α R = f → h =  (desc_to_Q α R β f hf) := 
begin
  let g := (desc_to_Q α R β f hf),
  have hg : g ∘ π α R = f, 
  { apply funext, intros x, 
    dsimp,
    apply desc_to_Q_spec,
    refl },
  split,
  { exact hg },
  { intros h H, 
    apply funext, intros q,
    obtain ⟨a,ha⟩ := π_surjective α R q,
    rewrite [← ha],
    change (h ∘ π α R ) a = (g ∘ π α R ) a,
    rewrite [H, hg] }
end

example : Type* := quotient R
example : α → quotient R := quotient.mk'
example (β : Type*) (f : α → β) (hf : ∀ a b : α, R.rel a b → f a = f b) : 
  quotient R → β := 
λ q, quotient.lift_on' q f hf
example (β : Type*) (f : α → β) (hf : ∀ a b : α, R.rel a b → f a = f b) :
  ∃! (g : quotient R → β), g ∘ quotient.mk' = f := 
⟨λ q, quotient.lift_on' q f hf, by { ext, refl }, λ h H, 
  by { ext ⟨x⟩, dsimp at H, convert congr_fun H x }⟩

noncomputable example : Q α R ≃ quotient R := 
{ to_fun := desc_to_Q _ _ _ quotient.mk' $ λ {x y : α}, quotient.eq_rel.mpr,
  inv_fun := λ q, quotient.lift_on' q (π _ _) sorry,
  left_inv := sorry,
  right_inv := sorry }

  example (G : Type*) [group G] (N : subgroup G) [subgroup.normal N] :
    (G ⧸ N) = quotient _ := rfl