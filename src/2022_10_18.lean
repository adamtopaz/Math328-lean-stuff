import group_theory.subgroup.basic
import group_theory.group_action.conj_act
import group_theory.group_action.group
import tactic.group

namespace test
variables 
  (G : Type*)  -- "Let G be a set"
  [group G] -- "And endow G with the structure of a group"


example : mul_action G G := infer_instance
example (a b : G) : a • b = a * b := rfl

example : conj_act G = G := rfl
example (a : conj_act G) (b : G) : a • b = a * b * a⁻¹ := rfl

@[derive group]
def Aut (G : Type*) [group G] := G ≃* G

instance : has_coe_to_fun (Aut G) (λ _, G → G) := ⟨λ e, e.to_fun⟩ 

def ρ : G →* Aut G := 
{ to_fun := λ g, 
  { to_fun := λ x, g * x * g⁻¹,
    inv_fun := λ x, g⁻¹ * x * g,
    left_inv := λ x, by group,
    right_inv := λ x, by group,
    map_mul' := λ x y, by group },
  map_one' := by tidy,
  map_mul' := begin
    intros g h, 
    ext x,
    dsimp,
    group,
  end }

def image_of_ρ : subgroup (Aut G) := (ρ G).range

theorem problem_3_on_homework_3 (t : image_of_ρ G) (e : Aut G) : 
  e * t * e⁻¹ ∈ image_of_ρ G := 
begin
  obtain ⟨_,g,rfl⟩ := t,
  change ∃ h, _,
  let h : G := e g,
  use h,
  ext x,
  dsimp [ρ],
  simp,
end
end test

variables {G : Type*} [group G]
variable (X : Type*) -- "Let X be a set"
variable [mul_action (G × G) X] -- "Suppose that G × G acts on X."


def σ : G × G ≃* G × G := 
{ to_fun := λ g, ⟨g.2,g.1⟩,
  inv_fun := λ g, ⟨g.2, g.1⟩,
  left_inv := by tidy,
  right_inv := by tidy,
  map_mul' := by tidy }

theorem problem_1_on_homework_3 
  (h : ∀ (x : X) (P : G × G), P • x = (σ P) • x) :
  ∀ a b ∈ (mul_action.to_perm_hom (G × G) X).range, a * b = b * a := 
begin
  intros a ha b hb,
  let ρ := (mul_action.to_perm_hom (G × G) X),
  have key_claim : ∀ g : G × G, ρ g = ρ (σ g),
  { intros g, ext x,
    dsimp [ρ,σ],
    apply h },
  obtain ⟨⟨g1,g2⟩,(rfl : ρ _ = _)⟩ := ha,
  obtain ⟨⟨h1,h2⟩,(rfl : ρ _ = _)⟩ := hb,
  have hg : (g1,g2) = (g1,1) * (1,g2), by tidy,
  have hh : (h1,h2) = (h1,1) * (1,h2), by tidy,
  rewrite [hg,hh],
  simp_rw [ρ.map_mul, ←mul_assoc],
  have claim1 : ρ (g1, 1) * ρ (1, g2) * ρ (h1, 1) * ρ (1, h2) = 
    ρ (g1, 1) * ρ (h1, 1) * ρ (1, g2)  * ρ (1, h2),
  { congr' 1, 
    simp_rw [mul_assoc],
    congr' 1,
    simp_rw [← ρ.map_mul],
    congr' 1,
    ext,
    dsimp,
    simp,
    dsimp, 
    simp },
  rewrite [claim1],
  have claim2 : ρ (g1, 1) * ρ (h1, 1) = ρ (h1,1) * ρ (g1,1),
  { rw key_claim (g1,1),
    simp_rw [← ρ.map_mul], 
    congr' 1,
    dsimp [σ], simp },
  rewrite [claim2],
  have claim3 : ρ (h1, 1) * ρ (g1, 1) * ρ (1, g2) * ρ (1, h2) = 
    ρ (h1, 1) * ρ (g1, 1) * ρ (1, h2) * ρ (1, g2),
  { simp_rw [mul_assoc], 
    congr' 2,
    rw key_claim (1,g2),
    simp_rw [← ρ.map_mul],
    congr' 1,
    dsimp [σ], simp },
  rewrite [claim3],
  have claim4 : ρ (h1, 1) * ρ (g1, 1) * ρ (1, h2) = 
    ρ (h1, 1) * ρ (1, h2) * ρ (g1, 1),
  { simp_rw [← ρ.map_mul], congr' 1, simp, },
  rewrite [claim4],
end


#check mul_action.to_perm_hom