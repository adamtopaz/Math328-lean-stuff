import group_theory.quotient_group

variables (G : Type*) [group G] (N : subgroup G) [subgroup.normal N]

def the_fourth_isomorphism_theorem : 
  subgroup (G ⧸ N) ≃o { K : subgroup G | N ≤ K } :=
let π : G →* G ⧸ N := quotient_group.mk' _ in
{ to_fun := λ H, 
  { val := H.comap π,
    property := begin
      dsimp, intros n hn,
      dsimp,
      have : (n : G ⧸ N) = 1, by simpa,
      rw this,
      apply H.one_mem,
    end },
  inv_fun := λ H, (H : subgroup G).map π,
  left_inv := begin
    intros H, dsimp,
    ext x,
    split,
    { intros hx, simp at hx, obtain ⟨y,hy,rfl⟩ := hx, assumption, },
    { intros hx, simp, obtain ⟨y,rfl⟩ := quotient_group.mk_surjective x, use [y, hx, rfl] }
  end,
  right_inv := begin
    rintros ⟨H,hH⟩, dsimp at hH, apply subtype.ext, dsimp,
    apply le_antisymm,
    { intros x hx, simp at hx, obtain ⟨y,h1,h2⟩ := hx, 
      have : y⁻¹ * x ∈ N,
      { rw ← quotient_group.eq, exact h2, },
      simpa using (H.mul_mem h1 (hH this)) },
    { exact subgroup.le_comap_map π H, }
  end,
  map_rel_iff' := begin
    intros A B,
    split,
    { intros H, dsimp at H, 
      intros a ha,
      obtain ⟨a,rfl⟩ := quotient_group.mk_surjective a,
      replace ha := H ha,
      exact ha },
    { intros H, dsimp, intros a ha,
      apply H,
      exact ha }
  end } 