/-
Copyright (c) 2025 Benoît Guillemet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benoît Guillemet
-/
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Sites.Canonical
import Mathlib.CategoryTheory.Limits.Types.Colimits
import Mathlib.CategoryTheory.Sites.Adjunction
import Mathlib.CategoryTheory.Sites.LeftExact

/-!
# Quasicompact and quasiseparated sheaves

Given a site `(C, J)`, we define structures for being quasicompact, quasiseparated
or qcqs sheaves.

-/

universe u v u' v' w

namespace CategoryTheory.Sheaf

open Category

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {A : Type u'} [Category.{v'} A] [HasWeakSheafify J A] [Limits.HasColimits A]

section Quasicompact

/-- A sheaf `F` is quasicompact if any cover `∐ G ⟶ F` admits a finite subcover. -/
structure Quasicompact (F : Sheaf J A) : Prop where
  isQuasicompact : ∀ {I : Type v'} {G : I → Sheaf J A} (f : ∐ G ⟶ F) [Epi f],
    ∃ J : Finset I, Epi ((Limits.Sigma.map' Subtype.val (fun (j : J) => 𝟙 (G j))) ≫ f)

theorem quasicompact_iff_finite_subcover (F : Sheaf J A) :
    Quasicompact F
    ↔ ∀ (I : Type v') (G : I → Sheaf J A) (f : ∐ G ⟶ F) [Epi f],
    ∃ J : Finset I, Epi ((Limits.Sigma.map' Subtype.val (fun (j : J) => 𝟙 (G j))) ≫ f) :=
  sorry

lemma quasicompact_of_finite_presieve_quasicompact (F : Sheaf J A) (I : Type v') (hI : Fintype I)
    (G : I → Sheaf J A) (hG : ∀ i : I, Quasicompact (G i)) (f : ∐ G ⟶ F) [Epi f] :
    F.Quasicompact where
  isQuasicompact f' := by
    sorry
    --choose J' hJ' using (fun i : I => hG i I' (fun i' => Limits.pullback (Sigma.ι i ≫ f) f') _)

end Quasicompact

variable [Limits.HasPullbacks A]

section Quasiseparated

/-- A morphism of sheaves `g : G ⟶ F` is quasicompact if the pullback of any morphism `F' ⟶ F`
  with quasicompact source is again quasicompact. -/
structure QuasicompactMap {F G : Sheaf J A} (g : G ⟶ F) : Prop where
  quasicompact_pullback : ∀ (F' : Sheaf J A) (f : F' ⟶ F),
    F'.Quasicompact → (Limits.pullback f g).Quasicompact

/-- A sheaf `F` is quasiseparated if any morphism `F' ⟶ F` with quasicompact source is
  quasicompact. -/
structure Quasiseparated (F : Sheaf J A) : Prop where
  isQuasiseparated : ∀ (F' : Sheaf J A) (f : F' ⟶ F), F'.Quasicompact → QuasicompactMap f

end Quasiseparated

section Qcqs

/-- A sheaf `F` is qcqs if it is both quasicompact and quasiseparated. -/
structure Qcqs (F : Sheaf J A) : Prop extends F.Quasicompact, F.Quasiseparated

end Qcqs

end CategoryTheory.Sheaf
