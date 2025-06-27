/-
Copyright (c) 2025 Benoît Guillemet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benoît Guillemet
-/
import Mathlib.CategoryTheory.Closed.Types
import Mathlib.CategoryTheory.Sites.Qcqs
import Mathlib.CategoryTheory.Sites.Adjunction
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Sites.ConcreteSheafification
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Sites.Continuous
import Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology
import Mathlib.Condensed.Functors
import Mathlib.Condensed.Limits

/-!
# Quasicompact and quasiseparated condensed sets

We give properties of quasicompact, quasiseparated and qcqs condensed sets.
-/

universe u v w

open CategoryTheory Limits

namespace Condensed

attribute [local instance] Types.instConcreteCategory

variable (X : CondensedSet.{u})

noncomputable def test (j : (sectionOver X.val)ᵒᵖ) :
    (((overYoneda' X.val) ⋙ presheafToSheaf (coherentTopology CompHaus) (Type (u+1))).obj j)
    ≅ (compHausToCondensed.obj j.unop.fst.unop) :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso
    (isoSheafify _ ((isSheaf_iff_isSheaf_of_type _ _).2 (Presieve.isSheaf_comp_uliftFunctor _
    (coherentTopology.isSheaf_yoneda_obj j.unop.fst.unop)))).symm

noncomputable def jsp' (n : ℕ) (S : Fin n → CompHaus.{u}ᵒᵖ) :
    ((lim (J := Discrete (Fin n)) (C := CompHaus.{u}ᵒᵖ))
    ⋙ evaluation CompHaus.{u}ᵒᵖ (Type (u + 1))
    ⋙ (whiskeringLeft _ _ _).obj (sheafToPresheaf (coherentTopology CompHaus) _)).obj (Discrete.functor S)
    ≅ (whiskeringLeft _ _ _
    ⋙ (whiskeringRight _ _ _).obj lim
    ⋙ (whiskeringLeft _ _ _).obj (sheafToPresheaf (coherentTopology CompHaus) _)).obj (Discrete.functor S) := by
  refine NatIso.ofComponents (fun X => preservesLimitIso X.val _) fun {Y Y'} f => ?_
  simp
  ext x j
  simp
  #check preservesLimitNatIso_hom_app
  sorry

noncomputable def jsp3 (n : ℕ) (S : (Discrete (Fin n))ᵒᵖ ⥤ CompHausᵒᵖ)
    (X : Sheaf (coherentTopology CompHaus) (Type (u + 1))) :
    (sheafToPresheaf (coherentTopology CompHaus) (Type (u + 1))
    ⋙ (evaluation CompHausᵒᵖ (Type (u + 1))).obj (limit S)).obj X
    ≅ (limit (S ⋙ evaluation _ _ ⋙ (whiskeringLeft _ _ _).obj (sheafToPresheaf _ _))).obj X := by
  refine Iso.trans ?_ (limitObjIsoLimitCompEvaluation _ X).symm
  simp
  sorry

noncomputable def jsp2 (n : ℕ) (S : (Discrete (Fin n))ᵒᵖ ⥤ CompHausᵒᵖ) :
    sheafToPresheaf (coherentTopology CompHaus) (Type (u + 1))
    ⋙ (evaluation CompHausᵒᵖ (Type (u + 1))).obj (limit S)
    ≅ limit (S ⋙ evaluation _ _ ⋙ (whiskeringLeft _ _ _).obj (sheafToPresheaf _ _)) := by
  sorry

noncomputable def jsp (n : ℕ) :
    (lim (J := (Discrete (Fin n))ᵒᵖ) (C := CompHaus.{u}ᵒᵖ))
    ⋙ evaluation CompHaus.{u}ᵒᵖ (Type (u + 1))
    ⋙ (whiskeringLeft _ _ _).obj (sheafToPresheaf (coherentTopology CompHaus) _)
    ≅ (whiskeringRight _ _ _).obj
    (evaluation _ _ ⋙ (whiskeringLeft _ _ _).obj (sheafToPresheaf _ _)) ⋙ lim := by
  sorry

noncomputable def limCompValNatIso {n : ℕ} (X : CondensedSet.{u}) :
    lim ⋙ X.val ≅ (whiskeringRight (Discrete (Fin n)) _ _).obj X.val ⋙ lim :=
  preservesLimitNatIso X.val

noncomputable def jsppp (n : ℕ) :
    sheafToPresheaf (coherentTopology CompHaus) (Type (u + 1))
    ⋙ (whiskeringLeft (Discrete (Fin n) ⥤ CompHausᵒᵖ) _ _).obj lim
    ≅ sheafToPresheaf (coherentTopology CompHaus) _ ⋙ whiskeringRight _ _ _
    ⋙ (whiskeringRight _ _ _).obj lim := by
  refine NatIso.ofComponents (fun X => preservesLimitNatIso X.val) fun {X Y} f => ?_
  simp
  ext S x j
  simp
  have : (preservesLimitIso Y.val S).hom (f.val.app (limit S) x)
      = limMap (((whiskeringRight _ _ _).map f.val).app S) ((preservesLimitIso X.val S).hom x) := by
    unfold preservesLimitIso
    sorry
  sorry

noncomputable def compHausToCondensedOpCompCoyoneda :
    compHausToCondensed.op ⋙ coyoneda
      ≅ evaluation _ _ ⋙ (whiskeringLeft _ _ _).obj (sheafToPresheaf _ _) :=
  (coherentTopology CompHaus).largeCurriedYonedaCompUliftFunctorLemma.trans
    (isoWhiskerLeft _ (isoWhiskerRight ((whiskeringRight _ _ _).mapIso uliftFunctorTrivial) _))

noncomputable def coyonedaOpCompHausToCondensedFiniteCoproductNatIso (n : ℕ)
    (X : Fin n → CompHaus.{u}) :
    coyoneda.obj (Opposite.op (compHausToCondensed.obj (∐ X)))
    ≅ coyoneda.obj (Opposite.op (∐ compHausToCondensed.obj ∘ X)) := by
  show ((coherentTopology CompHaus).yoneda.op
    ⋙ (sheafCompose _ uliftFunctor).op ⋙ coyoneda).obj (Opposite.op (∐ X)) ≅ _
  refine ((coherentTopology CompHaus).largeCurriedYonedaCompUliftFunctorLemma.app _).trans ?_
  refine (isoWhiskerLeft (sheafToPresheaf (coherentTopology CompHaus) (Type (u + 1)) ⋙ (evaluation _ _).obj _) uliftFunctorTrivial).trans ?_
  rw [Functor.comp_id]
  refine Iso.trans ?_ ((preservesLimitIso coyoneda _).symm.trans (coyoneda.mapIso (limitOpIsoOpColimit _)))
  refine (isoWhiskerLeft _ ((evaluation _ _).mapIso (limitOpIsoOpColimit _).symm)).trans ?_
  refine Iso.trans ?_ (HasLimit.isoOfNatIso (isoWhiskerRight (NatIso.op (Discrete.compNatIsoDiscrete _ _).symm) _))
  refine Iso.trans ?_ (HasLimit.isoOfNatIso (isoWhiskerLeft (Discrete.functor X).op compHausToCondensedOpCompCoyoneda.symm))

  sorry

noncomputable def compHausToCondensed_finiteCoproduct {n : ℕ} (X : Fin n → CompHaus.{u}) :
    compHausToCondensed.obj (∐ X) ≅ ∐ (compHausToCondensed.obj ∘ X) :=
  (Coyoneda.fullyFaithful.preimageIso
    (coyonedaOpCompHausToCondensedFiniteCoproductNatIso n X).symm).unop

theorem isQuasicompact_iff_compHaus_cover (X : CondensedSet.{u}) :
    X.Quasicompact ↔ ∃ S : CompHaus.{u}, ∃ f : compHausToCondensed.obj S ⟶ X, Epi f := by
  constructor
  · intro hX
    obtain ⟨J, hJ⟩ := hX.isQuasicompact
      (Limits.sigmaMapColim (overYoneda' X.val ⋙ presheafToSheaf _ _)
      ≫ (Sheaf.isoColimitOverYonedaCompPresheafToSheaf'.{u + 1} X).inv)
    obtain ⟨n, hn⟩ := Finite.exists_equiv_fin J
    obtain e := Classical.choice hn
    use CompHausLike.finiteCoproduct.{0, u} (fun j : Fin n => (e.invFun j).val.unop.fst.unop)
    sorry
  sorry
