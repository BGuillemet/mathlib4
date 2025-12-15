/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Ulift
public import Mathlib.CategoryTheory.Sites.Canonical
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Sites.Closed
public import Mathlib.CategoryTheory.Sites.Coverage
/-!

# Subcanonical Grothendieck topologies

This file provides some API for the Yoneda embedding into the category of sheaves for a
subcanonical Grothendieck topology.
-/

@[expose] public section

universe v' v u

namespace CategoryTheory.GrothendieckTopology

open Opposite Functor

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) [Subcanonical J]

/--
The equivalence between natural transformations from the yoneda embedding (to the sheaf category)
and elements of `F.val.obj X`.
-/
def yonedaEquiv {X : C} {F : Sheaf J (Type v)} : (J.yoneda.obj X ⟶ F) ≃ F.val.obj (op X) :=
  (fullyFaithfulSheafToPresheaf _ _).homEquiv.trans CategoryTheory.yonedaEquiv

theorem yonedaEquiv_apply {X : C} {F : Sheaf J (Type v)} (f : J.yoneda.obj X ⟶ F) :
    yonedaEquiv J f = f.val.app (op X) (𝟙 X) :=
  rfl

@[simp]
theorem yonedaEquiv_symm_app_apply {X : C} {F : Sheaf J (Type v)} (x : F.val.obj (op X)) (Y : Cᵒᵖ)
    (f : Y.unop ⟶ X) : (J.yonedaEquiv.symm x).val.app Y f = F.val.map f.op x :=
  rfl

/-- See also `yonedaEquiv_naturality'` for a more general version. -/
lemma yonedaEquiv_naturality {X Y : C} {F : Sheaf J (Type v)} (f : J.yoneda.obj X ⟶ F)
    (g : Y ⟶ X) : F.val.map g.op (J.yonedaEquiv f) = J.yonedaEquiv (J.yoneda.map g ≫ f) := by
  simp [yonedaEquiv, CategoryTheory.yonedaEquiv_naturality]
  rfl

/--
Variant of `yonedaEquiv_naturality` with general `g`. This is technically strictly more general
than `yonedaEquiv_naturality`, but `yonedaEquiv_naturality` is sometimes preferable because it
can avoid the "motive is not type correct" error.
-/
lemma yonedaEquiv_naturality' {X Y : Cᵒᵖ} {F : Sheaf J (Type v)} (f : J.yoneda.obj (unop X) ⟶ F)
    (g : X ⟶ Y) : F.val.map g (J.yonedaEquiv f) = J.yonedaEquiv (J.yoneda.map g.unop ≫ f) :=
  J.yonedaEquiv_naturality _ _

lemma yonedaEquiv_comp {X : C} {F G : Sheaf J (Type v)} (α : J.yoneda.obj X ⟶ F) (β : F ⟶ G) :
    J.yonedaEquiv (α ≫ β) = β.val.app _ (J.yonedaEquiv α) :=
  rfl

lemma yonedaEquiv_yoneda_map {X Y : C} (f : X ⟶ Y) : J.yonedaEquiv (J.yoneda.map f) = f := by
  rw [yonedaEquiv_apply]
  simp

lemma yonedaEquiv_symm_naturality_left {X X' : C} (f : X' ⟶ X) (F : Sheaf J (Type v))
    (x : F.val.obj ⟨X⟩) : J.yoneda.map f ≫ J.yonedaEquiv.symm x = J.yonedaEquiv.symm
      ((F.val.map f.op) x) := by
  apply J.yonedaEquiv.injective
  simp only [yonedaEquiv_comp, yonedaEquiv_symm_app_apply, Equiv.apply_symm_apply]
  rw [yonedaEquiv_yoneda_map]

lemma yonedaEquiv_symm_naturality_right (X : C) {F F' : Sheaf J (Type v)} (f : F ⟶ F')
    (x : F.val.obj ⟨X⟩) : J.yonedaEquiv.symm x ≫ f = J.yonedaEquiv.symm (f.val.app ⟨X⟩ x) := by
  apply J.yonedaEquiv.injective
  simp [yonedaEquiv_comp]

/-- See also `map_yonedaEquiv'` for a more general version. -/
lemma map_yonedaEquiv {X Y : C} {F : Sheaf J (Type v)} (f : J.yoneda.obj X ⟶ F)
    (g : Y ⟶ X) : F.val.map g.op (J.yonedaEquiv f) = f.val.app (op Y) g := by
  rw [yonedaEquiv_naturality, yonedaEquiv_comp, yonedaEquiv_yoneda_map]

/--
Variant of `map_yonedaEquiv` with general `g`. This is technically strictly more general
than `map_yonedaEquiv`, but `map_yonedaEquiv` is sometimes preferable because it
can avoid the "motive is not type correct" error.
-/
lemma map_yonedaEquiv' {X Y : Cᵒᵖ} {F : Sheaf J (Type v)} (f : J.yoneda.obj (unop X) ⟶ F)
    (g : X ⟶ Y) : F.val.map g (J.yonedaEquiv f) = f.val.app Y g.unop := by
  rw [yonedaEquiv_naturality', yonedaEquiv_comp, yonedaEquiv_yoneda_map]

lemma yonedaEquiv_symm_map {X Y : Cᵒᵖ} (f : X ⟶ Y) {F : Sheaf J (Type v)} (t : F.val.obj X) :
    J.yonedaEquiv.symm (F.val.map f t) = J.yoneda.map f.unop ≫ J.yonedaEquiv.symm t := by
  obtain ⟨u, rfl⟩ := J.yonedaEquiv.surjective t
  rw [yonedaEquiv_naturality', Equiv.symm_apply_apply, Equiv.symm_apply_apply]

/--
Two morphisms of sheaves of types `P ⟶ Q` coincide if the precompositions with morphisms
`yoneda.obj X ⟶ P` agree.
-/
lemma hom_ext_yoneda {P Q : Sheaf J (Type v)} {f g : P ⟶ Q}
    (h : ∀ (X : C) (p : J.yoneda.obj X ⟶ P), p ≫ f = p ≫ g) :
    f = g := by
  ext X x
  simpa only [yonedaEquiv_comp, Equiv.apply_symm_apply]
    using congr_arg (J.yonedaEquiv) (h _ (J.yonedaEquiv.symm x))

/-- The curried version of the Yoneda lemma for sheaves. -/
def largeCurriedYonedaLemma :
    J.yoneda.op ⋙ coyoneda ≅
      evaluation Cᵒᵖ (Type v) ⋙ (whiskeringRight _ _ _).obj uliftFunctor.{u}
      ⋙ (whiskeringLeft _ _ _).obj (sheafToPresheaf _ _) :=
  ((isoWhiskerLeft _ sheafToPresheafCompCoyonedaCompWhiskeringLeftSheafToPresheaf.symm).trans
    (isoWhiskerRight (NatIso.op J.yonedaCompSheafToPresheaf.symm)
    (_ ⋙ (whiskeringLeft _ _ _).obj _))).trans
    (isoWhiskerRight CategoryTheory.largeCurriedYonedaLemma ((whiskeringLeft _ _ _).obj _))

@[simp]
lemma largeCurriedYonedaLemma_app_app (X : C) (F : Sheaf J (Type v)) :
    (J.largeCurriedYonedaLemma.app (op X)).app F
    = (J.yonedaEquiv.trans Equiv.ulift.symm).toIso :=
  rfl

/-- A version of `yonedaEquiv` for `uliftYoneda`. -/
def uliftYonedaEquiv {X : C} {F : Sheaf J (Type (max v v'))} :
    ((uliftYoneda.{v'} J).obj X ⟶ F) ≃ F.val.obj (op X) :=
  (fullyFaithfulSheafToPresheaf _ _).homEquiv.trans CategoryTheory.uliftYonedaEquiv

@[deprecated (since := "2025-11-10")] alias yonedaULiftEquiv := uliftYonedaEquiv

theorem uliftYonedaEquiv_apply {X : C} {F : Sheaf J (Type (max v v'))}
    (f : J.uliftYoneda.obj X ⟶ F) : uliftYonedaEquiv.{v'} J f = f.val.app (op X) ⟨𝟙 X⟩ :=
  rfl

@[deprecated (since := "2025-11-10")] alias yonedaULiftEquiv_apply := uliftYonedaEquiv_apply

@[simp]
theorem uliftYonedaEquiv_symm_app_apply {X : C} {F : Sheaf J (Type (max v v'))}
    (x : F.val.obj (op X)) (Y : Cᵒᵖ) (f : Y.unop ⟶ X) :
    (J.uliftYonedaEquiv.symm x).val.app Y ⟨f⟩ = F.val.map f.op x :=
  rfl

@[deprecated (since := "2025-11-10")] alias yonedaULiftEquiv_symm_app_apply :=
  uliftYonedaEquiv_symm_app_apply

/-- See also `uliftYonedaEquiv_naturality'` for a more general version. -/
lemma uliftYonedaEquiv_naturality {X Y : C} {F : Sheaf J (Type (max v v'))}
    (f : J.uliftYoneda.obj X ⟶ F) (g : Y ⟶ X) :
      F.val.map g.op (J.uliftYonedaEquiv f) = J.uliftYonedaEquiv (J.uliftYoneda.map g ≫ f) := by
  change (f.val.app (op X) ≫ F.val.map g.op) ⟨𝟙 X⟩ = f.val.app (op Y) ⟨𝟙 Y ≫ g⟩
  rw [← f.val.naturality]
  simp [uliftYoneda]

@[deprecated (since := "2025-11-10")] alias yonedaULiftEquiv_naturality :=
  uliftYonedaEquiv_naturality

/-- Variant of `uliftYonedaEquiv_naturality` with general `g`. This is technically strictly more
general than `uliftYonedaEquiv_naturality`, but `uliftYonedaEquiv_naturality` is sometimes
preferable because it can avoid the "motive is not type correct" error. -/
lemma uliftYonedaEquiv_naturality' {X Y : Cᵒᵖ} {F : Sheaf J (Type (max v v'))}
    (f : J.uliftYoneda.obj (unop X) ⟶ F) (g : X ⟶ Y) :
    F.val.map g (J.uliftYonedaEquiv f) = J.uliftYonedaEquiv (J.uliftYoneda.map g.unop ≫ f) :=
  J.uliftYonedaEquiv_naturality _ _

@[deprecated (since := "2025-11-10")] alias yonedaULiftEquiv_naturality' :=
  uliftYonedaEquiv_naturality'

lemma uliftYonedaEquiv_comp {X : C} {F G : Sheaf J (Type (max v v'))} (α : J.uliftYoneda.obj X ⟶ F)
    (β : F ⟶ G) : J.uliftYonedaEquiv (α ≫ β) = β.val.app _ (J.uliftYonedaEquiv α) :=
  rfl

@[deprecated (since := "2025-11-10")] alias yonedaULiftEquiv_comp := uliftYonedaEquiv_comp

lemma uliftYonedaEquiv_uliftYoneda_map {X Y : C} (f : X ⟶ Y) :
    (uliftYonedaEquiv.{v'} J) (J.uliftYoneda.map f) = ⟨f⟩ := by
  rw [uliftYonedaEquiv_apply]
  simp [uliftYoneda]

@[deprecated (since := "2025-11-10")] alias yonedaULiftEquiv_yonedaULift_map :=
  uliftYonedaEquiv_uliftYoneda_map

lemma uliftYonedaEquiv_symm_naturality_left {X X' : C} (f : X' ⟶ X) (F : Sheaf J (Type (max v v')))
    (x : F.val.obj ⟨X⟩) :
    J.uliftYoneda.map f ≫ J.uliftYonedaEquiv.symm x =
      J.uliftYonedaEquiv.symm ((F.val.map f.op) x) := by
  apply J.uliftYonedaEquiv.injective
  simp only [uliftYonedaEquiv_comp, Equiv.apply_symm_apply]
  rw [uliftYonedaEquiv_uliftYoneda_map]
  rfl

@[deprecated (since := "2025-11-10")] alias yonedaULiftEquiv_symm_naturality_left :=
  uliftYonedaEquiv_symm_naturality_left

lemma uliftYonedaEquiv_symm_naturality_right (X : C) {F F' : Sheaf J (Type (max v v'))}
    (f : F ⟶ F') (x : F.val.obj ⟨X⟩) :
    J.uliftYonedaEquiv.symm x ≫ f = J.uliftYonedaEquiv.symm (f.val.app ⟨X⟩ x) := by
  apply J.uliftYonedaEquiv.injective
  simp [uliftYonedaEquiv_comp]

@[deprecated (since := "2025-11-10")] alias yonedaULiftEquiv_symm_naturality_right :=
  uliftYonedaEquiv_symm_naturality_right

/-- See also `map_yonedaEquiv'` for a more general version. -/
lemma map_uliftYonedaEquiv {X Y : C} {F : Sheaf J (Type (max v v'))}
    (f : J.uliftYoneda.obj X ⟶ F) (g : Y ⟶ X) :
    F.val.map g.op (J.uliftYonedaEquiv f) = f.val.app (op Y) ⟨g⟩ := by
  rw [uliftYonedaEquiv_naturality, uliftYonedaEquiv_comp, uliftYonedaEquiv_uliftYoneda_map]

@[deprecated (since := "2025-11-10")] alias map_yonedaULiftEquiv := map_uliftYonedaEquiv

/-- Variant of `map_uliftYonedaEquiv` with general `g`. This is technically strictly more general
than `map_uliftYonedaEquiv`, but `map_uliftYonedaEquiv` is sometimes preferable because it
can avoid the "motive is not type correct" error. -/
lemma map_uliftYonedaEquiv' {X Y : Cᵒᵖ} {F : Sheaf J (Type (max v v'))}
    (f : J.uliftYoneda.obj (unop X) ⟶ F) (g : X ⟶ Y) :
    F.val.map g (J.uliftYonedaEquiv f) = f.val.app Y ⟨g.unop⟩ := by
  rw [uliftYonedaEquiv_naturality', uliftYonedaEquiv_comp, uliftYonedaEquiv_uliftYoneda_map]

@[deprecated (since := "2025-11-10")] alias map_yonedaULiftEquiv' := map_uliftYonedaEquiv'

lemma uliftYonedaEquiv_symm_map {X Y : Cᵒᵖ} (f : X ⟶ Y) {F : Sheaf J (Type (max v v'))}
    (t : F.val.obj X) : J.uliftYonedaEquiv.symm (F.val.map f t) =
      J.uliftYoneda.map f.unop ≫ J.uliftYonedaEquiv.symm t := by
  obtain ⟨u, rfl⟩ := J.uliftYonedaEquiv.surjective t
  rw [uliftYonedaEquiv_naturality', Equiv.symm_apply_apply, Equiv.symm_apply_apply]

@[deprecated (since := "2025-11-10")] alias yonedaULiftEquiv_symm_map := uliftYonedaEquiv_symm_map

/-- Two morphisms of sheaves of types `P ⟶ Q` coincide if the precompositions
with morphisms `uliftYoneda.obj X ⟶ P` agree. -/
lemma hom_ext_uliftYoneda {P Q : Sheaf J (Type (max v v'))} {f g : P ⟶ Q}
    (h : ∀ (X : C) (p : J.uliftYoneda.obj X ⟶ P), p ≫ f = p ≫ g) :
    f = g := by
  ext X x
  simpa only [uliftYonedaEquiv_comp, Equiv.apply_symm_apply]
    using congr_arg (J.uliftYonedaEquiv) (h _ (J.uliftYonedaEquiv.symm x))

@[deprecated (since := "2025-11-10")] alias hom_ext_yonedaULift := hom_ext_uliftYoneda

/-- A variant of the curried version of the Yoneda lemma with a raise in the universe level. -/
def largeCurriedUliftYonedaLemma :
    J.uliftYoneda.op ⋙ coyoneda ≅
      evaluation Cᵒᵖ (Type max v v') ⋙ (whiskeringRight _ _ _).obj uliftFunctor.{u}
      ⋙ (whiskeringLeft _ _ _).obj (sheafToPresheaf _ _) :=
  ((isoWhiskerLeft (J.yoneda.op ⋙ (sheafCompose J _).op)
    sheafToPresheafCompCoyonedaCompWhiskeringLeftSheafToPresheaf.symm).trans
    (isoWhiskerRight (NatIso.op (J.uliftYonedaCompSheafToPresheaf.symm))
    (_ ⋙ (whiskeringLeft _ _ _).obj _))).trans
    (isoWhiskerRight CategoryTheory.uliftYonedaOpCompCoyoneda
    ((whiskeringLeft _ _ _).obj _))

@[simp]
lemma largeCurriedUliftYonedaLemma_app_app (X : C) (F : Sheaf J (Type (max v v'))) :
    (J.largeCurriedUliftYonedaLemma.app (op X)).app F
    = (J.uliftYonedaEquiv.trans Equiv.ulift.symm).toIso :=
  rfl

abbrev familyOfElementsPtVal {X : C} {S : Sieve X}
    (s : Limits.Cocone (S.arrows.diagram ⋙ J.yoneda)) :
    S.arrows.FamilyOfElements s.pt.val :=
  (fun _ f hf => J.yonedaEquiv (s.ι.app ⟨Over.mk f, hf⟩))

theorem familyOfElementsPtVal_compatible {X : C} {S : Sieve X}
    (s : Limits.Cocone (S.arrows.diagram ⋙ J.yoneda)) :
    (J.familyOfElementsPtVal s).Compatible := by
  refine (Presieve.compatible_iff_sieveCompatible _).2 (fun Y Z f g hf => ?_)
  rw [yonedaEquiv_naturality]
  let : ({ obj := Over.mk (g ≫ f), property := S.downward_closed hf g } : S.arrows.category)
      ⟶ { obj := Over.mk f, property := hf} :=
    Over.homMk g
  simp only [id_obj, ← s.w this, comp_obj, ObjectProperty.ι_obj, Over.forget_obj,
    Over.mk_left, const_obj_obj, Functor.comp_map, ObjectProperty.ι_map, Over.forget_map,
    EmbeddingLike.apply_eq_iff_eq]
  rfl

@[simps]
def compatibleYonedaFamily_toCocone (F : Sheaf J (Type v)) {X : C} (R : Presieve X)
    (x : Presieve.FamilyOfElements F.val R) (hx : x.Compatible) :
    Limits.Cocone (R.diagram ⋙ J.yoneda) where
  pt := F
  ι := {
    app := fun ⟨f, hf⟩ => J.yonedaEquiv.invFun (x f.hom hf)
    naturality := fun ⟨f, hf⟩ ⟨g, hg⟩ φ => by
      simp [J.yonedaEquiv_symm_naturality_left, hx φ.left (𝟙 _) hg hf]
    }

theorem isSheaf_sup (K L : GrothendieckTopology C) (P : Cᵒᵖ ⥤ Type max u v) :
    Presieve.IsSheaf (K ⊔ L) P ↔ Presieve.IsSheaf K P ∧ Presieve.IsSheaf L P := by
  rw [← (Coverage.gi C).l_u_eq K, ← (Coverage.gi C).l_u_eq L, ← (Coverage.gi C).gc.l_sup,
    Presieve.isSheaf_sup, (Coverage.gi C).l_u_eq K, (Coverage.gi C).l_u_eq L]

omit [J.Subcanonical] in
theorem mem_of_isSheafFor_pullback (X : C) (S : Sieve X)
    (hS : ∀ (F : Sheaf J (Type max u v)) {Y : C} {f : Y ⟶ X},
      Presieve.IsSheafFor F.val (S.pullback f).arrows) :
    S ∈ J X := by
  let J₂ := J ⊔ (S.arrows.skyscraperPrecoverage.toGrothendieck')
  have : J = J₂ := by
    refine topology_eq_iff_same_sheaves.2 (fun P => ?_)
    constructor <;> intro hP
    · unfold J₂
      refine (isSheaf_sup _ _ _).2 ⟨hP, ?_⟩
      rw [S.arrows.skyscraperPrecoverage.isSheaf_toGrothendieck'_iff]
      intro Y Z f R hR
      cases hR
      rw [Sieve.generate_sieve]
      exact hS ⟨P, (isSheaf_iff_isSheaf_of_type J P).2 hP⟩
    · exact Presieve.isSheaf_of_le P le_sup_left hP
  rw [this]
  apply le_sup_right (a := J)
  rw [← S.generate_sieve]
  apply Precoverage.generate_mem_toGrothendieck'
  simp

@[simps!]
def _root_.CategoryTheory.Sieve.pullbackFunctorNatTrans {X Y : C} (S : Sieve X) (f : Y ⟶ X) :
    (S.pullback f).functor ⟶ S.functor where
  app Z := fun ⟨g, hg⟩ => ⟨g ≫ f, hg⟩

theorem _root_.CategoryTheory.Sieve.isPullback {X Y : C} (S : Sieve X) (f : Y ⟶ X) :
    IsPullback (S.pullback f).functorInclusion (S.pullbackFunctorNatTrans f)
      (CategoryTheory.yoneda.map f) S.functorInclusion := by
  have (t : Limits.PullbackCone (CategoryTheory.yoneda.map f) S.functorInclusion) (Z : Cᵒᵖ)
      (s : t.pt.obj Z) : t.fst.app Z s ≫ f = (t.snd.app Z s).1 := by
    change (t.fst ≫ CategoryTheory.yoneda.map f).app Z s = (t.snd ≫ S.functorInclusion).app Z s
    rw [t.condition]
  refine IsPullback.mk { w := rfl } ⟨Limits.PullbackCone.IsLimit.mk _ ?_ ?_ ?_ ?_⟩ <;> intro t
  · refine NatTrans.mk (fun Z => ?_) (fun Z Z' g => ?_)
    · refine fun s => ⟨t.fst.app Z s, ?_⟩
      rw [Sieve.pullback_apply, this]
      exact (t.snd.app Z s).2
    · ext s
      apply Subtype.ext
      change (t.pt.map g ≫ t.fst.app Z') s = _
      rw [t.fst.naturality]
      rfl
  · ext Z s
    simp
  · ext Z s
    apply Subtype.ext
    simp [this]
  · intro m hm _
    ext Z s
    apply Subtype.ext
    change (m ≫ (Sieve.pullback f S).functorInclusion).app Z s = t.fst.app Z s
    rw [hm]

noncomputable def _root_.CategoryTheory.Sieve.pullbackFunctorIsoPullback {X Y : C} (S : Sieve X)
    (f : Y ⟶ X) :
    (Sieve.pullback f S).functor ≅
      Limits.pullback (CategoryTheory.yoneda.map f) S.functorInclusion :=
  (S.isPullback f).isoPullback

@[simps!]
def _root_.CategoryTheory.Sieve.functorDiagram {X : C} (S : Sieve X) :
    S.arrows.category ⥤ Cᵒᵖ ⥤ Type max u v :=
  S.arrows.diagram ⋙ CategoryTheory.uliftYoneda

def _root_.CategoryTheory.Sieve.functorCocone {X : C} (S : Sieve X) :
    Limits.Cocone S.functorDiagram where
  pt := S.functor ⋙ uliftFunctor
  ι := {
      app := fun ⟨⟨Y, _, f⟩, hY⟩ =>
        NatTrans.mk (fun Z ⟨g⟩ => { down := ⟨g ≫ f, S.downward_closed hY g⟩ })
      naturality := by
        intro ⟨⟨Y, _, g⟩, hY⟩ ⟨⟨Z, _, h⟩, hY⟩ ⟨f, _, hf⟩
        simp only [id_obj, const_obj_obj, Functor.id_map, const_obj_map, Category.comp_id] at hf
        ext W ⟨i⟩
        simp [hf]
    }

theorem isRepresentable_of_natIso' (F : Cᵒᵖ ⥤ Type*) {G} (i : F ≅ G) [F.IsRepresentable] :
    G.IsRepresentable :=
  (F.representableBy.ofIso i).isRepresentable

variable [HasWeakSheafify (Sheaf.canonicalTopology C) (Type max u v)] (F : Cᵒᵖ ⥤ Type max u v)

def _root_.CategoryTheory.sectionProperty : ObjectProperty (Over F) :=
  fun G => IsRepresentable G.1

def _root_.CategoryTheory.sectionCategory := (sectionProperty F).FullSubcategory

instance : Category (sectionCategory F) := ObjectProperty.FullSubcategory.category _

instance (G : sectionCategory F) : IsRepresentable G.1.1 := G.2

@[simps! obj_left obj_hom]
def _root_.CategoryTheory.sectionMk {X : C} (s : F.obj (Opposite.op X)) : sectionCategory F where
  obj := Over.mk (CategoryTheory.uliftYonedaEquiv.symm s)
  property := by
    unfold sectionProperty
    rw [Over.mk_left]
    infer_instance

@[simps!]
def _root_.CategoryTheory.sectionMkHom (G : sectionCategory F) {X : Cᵒᵖ} (s : G.obj.left.obj X) :
    sectionMk F (G.obj.hom.app X s) ⟶ G := by
  refine Over.homMk (CategoryTheory.uliftYonedaEquiv.symm s) ?_
  simp only [id_obj, const_obj_obj, sectionMk_obj_left, op_unop, sectionMk_obj_hom]
  rw [Equiv.eq_symm_apply, CategoryTheory.uliftYonedaEquiv_comp, Equiv.apply_symm_apply]

@[simps! left_app]
def _root_.CategoryTheory.sectionHomMk {X Y : C} (s : F.obj (Opposite.op X)) (f : Y ⟶ X) :
    sectionMk F (F.map f.op s) ⟶ sectionMk F s :=
  Over.homMk (CategoryTheory.uliftYoneda.map f)

open Limits in
@[simps!]
def _root_.CategoryTheory.sectionCocone : Cocone ((sectionProperty F).ι ⋙ Over.forget _) where
  pt := F
  ι := NatTrans.mk (fun ⟨X, _⟩ => X.hom)

def _root_.CategoryTheory.isColimitSectionCocone : Limits.IsColimit (sectionCocone F) where
  desc c := by
    refine NatTrans.mk (fun X s => (c.ι.app (sectionMk F s)).app X { down := 𝟙 _ }) ?_
    intro X Y f
    ext s
    let ι_app : _ ⟶ c.pt := c.ι.app (sectionMk F s)
    change (c.ι.app (sectionMk F (F.map f.unop.op s))).app Y _ = (ι_app.app X ≫ c.pt.map f) _
    rw [← ι_app.naturality, ← c.w (sectionHomMk F s f.unop)]
    simp [ι_app]
  fac c := by
    intro G
    ext Y s
    simp [← c.w (sectionMkHom F G s)]
  uniq c m h := by
    ext X s
    simp only [← h, sectionCocone_ι_app, FunctorToTypes.comp, sectionMk_obj_hom,
      uliftYonedaEquiv_symm_apply_app, op_id, FunctorToTypes.map_id_apply]

omit [J.Subcanonical] [HasWeakSheafify (Sheaf.canonicalTopology C) (Type max u v)] in
variable [HasWeakSheafify J (Type max u v)] in
theorem isColimitPresheafToSheafMapCoconeSectionCocone :
    Nonempty (Limits.IsColimit
      ((presheafToSheaf J (Type max u v)).mapCocone (sectionCocone F))) :=
  (Adjunction.leftAdjoint_preservesColimits
    (sheafificationAdjunction J (Type max u v))).preservesColimitsOfShape.preservesColimit.preserves
    (isColimitSectionCocone F)

abbrev _root_.CategoryTheory.Sieve.uliftFunctor {X : C} (S : Sieve X) : Cᵒᵖ ⥤ Type max u v :=
  S.functor ⋙ CategoryTheory.uliftFunctor.{u}

@[simps! app]
def _root_.CategoryTheory.Sieve.homFunctor {X Y : C} {S : Sieve X} {f : Y ⟶ X} (hf : S f) :
    CategoryTheory.uliftYoneda.obj Y ⟶ S.uliftFunctor :=
  NatTrans.mk (fun _ g => { down := ⟨g.down ≫ f, S.downward_closed hf g.down⟩ })

def _root_.CategoryTheory.Sieve.functorSectionPropertyFullSubcategory {X : C} (S : Sieve X) :
    S.arrows.category ⥤ (sectionProperty S.uliftFunctor).FullSubcategory where
  obj f := by
    refine { obj := Over.mk (S.homFunctor f.property), property := ?_ }
    simp only [sectionProperty, Over.mk_left]
    infer_instance
  map φ := Over.homMk (CategoryTheory.uliftYoneda.map φ.left)
  map_id _ := Over.OverMorphism.ext (by simp [ObjectProperty.FullSubcategory.id_def])
  map_comp _ _ := Over.OverMorphism.ext (by simp [ObjectProperty.FullSubcategory.comp_def])

def _root_.CategoryTheory.Sieve.functorArrowsCategory {X : C} (S : Sieve X) :
    (sectionProperty (S.functor ⋙ uliftFunctor)).FullSubcategory ⥤ S.arrows.category where
  obj := by
    intro ⟨⟨F, _, f⟩, (_ : F.IsRepresentable)⟩
    have := (CategoryTheory.uliftYonedaEquiv
      ((RepresentableBy.equivUliftYonedaIso _ _ F.representableBy).hom ≫ f)).down
    exact ⟨Over.mk this.1, this.2⟩
  map := by
    intro ⟨⟨F, _, f⟩, (_ : F.IsRepresentable)⟩ ⟨⟨G, _, g⟩, (_ : G.IsRepresentable)⟩ φ
    refine Over.homMk ((CategoryTheory.ULiftYoneda.fullyFaithful _).preimage (F.uliftReprW.hom ≫ φ.left ≫ G.uliftReprW.inv)) ?_
    apply (CategoryTheory.ULiftYoneda.fullyFaithful.{u} _).map_injective
    ext Y h
    simp at h
    simp [CategoryTheory.uliftYonedaEquiv]
    sorry

def nfdjkzl {X : C} (S : Sieve X) :
    (sectionProperty (S.functor ⋙ uliftFunctor)).FullSubcategory ≅ S.arrows.category :=
  sorry


theorem hfjklzhg {X : C} (S : Sieve X) : S.functorDiagram ≅ (sectionProperty S.functor).ι ⋙ Over.forget _ := by
  sorry

def fjkzmjaf {X : C} (S : Sieve X) : S.functorCocone ≅ sectionCocone S.functor

theorem fkemzjf {X : C} (S : Sieve X) : Nonempty (Limits.IsColimit S.functorCocone)

/-- A sieve of `X` belongs to a subcanonical topology `J` if and only if `yoneda X` is a colimit
  of the diagram associated to `S` composed with the Yoneda embedding into `Sheaf J (Type v)`. -/
theorem covering_iff_colimit_yoneda {X : C} (S : Sieve X) :
    S ∈ J X ↔ Nonempty (Limits.IsColimit (J.yoneda.mapCocone S.arrows.cocone)) := by
  constructor
  · exact fun hS => Nonempty.intro {
      desc s := J.yonedaEquiv.invFun ((s.pt.cond.isSheafFor S hS).amalgamate
        (J.familyOfElementsPtVal s) (J.familyOfElementsPtVal_compatible s))
      fac s j := by
        simp only [id_obj, comp_obj, ObjectProperty.ι_obj, Over.forget_obj, mapCocone_pt,
          Limits.Cocone.whisker_pt, Over.forgetCocone_pt, const_obj_obj, mapCocone_ι_app,
          Limits.Cocone.whisker_ι, whiskerLeft_app, Over.forgetCocone_ι_app, Equiv.invFun_as_coe,
          yonedaEquiv_symm_naturality_left, Presieve.IsSheafFor.valid_glue _ _ _ j.property,
          familyOfElementsPtVal, J.yonedaEquiv.symm_apply_apply]
        rfl
      uniq s m hm := by
        have h := (s.pt.cond.isSheafFor S hS) (J.familyOfElementsPtVal s)
          (J.familyOfElementsPtVal_compatible s)
        refine J.yonedaEquiv.eq_symm_apply.2 (h.unique ?_ ?_)
        · intro _ _ _
          rw [familyOfElementsPtVal, J.yonedaEquiv_naturality m, ← hm]
          rfl
        · exact (s.pt.cond.isSheafFor S hS).isAmalgamation (familyOfElementsPtVal_compatible J s)
      }
  · refine fun ⟨h⟩ => J.mem_of_isSheafFor_pullback _ _ (fun F Y f => ?_)
    have : Limits.IsColimit S.functorCocone := {
      desc s := by
        change S.functor ⋙ uliftFunctor ⟶ s.pt

    }
    have : IsIso S.functorInclusion := by
      sorry
    have : Limits.IsColimit (J.yoneda.mapCocone (S.pullback f).arrows.cocone) := by
      sorry
    have (F : Sheaf J (Type v)) : Presieve.IsSheafFor F.val S.arrows := by
      refine fun x hx => ?_
      use J.yonedaEquiv (h.desc (J.compatibleYonedaFamily_toCocone _ _ x hx))
      constructor
      · intro _ f hf
        rw [J.yonedaEquiv_naturality]
        have : J.yoneda.map f = (J.yoneda.mapCocone S.arrows.cocone).ι.app ⟨Over.mk f, hf⟩ :=
          rfl
        rw [this, h.fac]
        simp
      · intro a ha
        rw [← h.uniq _ (J.yonedaEquiv.invFun a)
          fun ⟨_, hf⟩ => by simp [yonedaEquiv_symm_naturality_left, ha _ hf]]
        exact J.yonedaEquiv.symm_apply_eq.1 rfl
    sorry

open Limits Opposite

def isColimitGenerate {X : C} (S : Presieve X) :
    Nonempty (IsColimit (J.yoneda.mapCocone (Sieve.generate S).arrows.cocone)) ↔
      Nonempty (IsColimit (J.yoneda.mapCocone S.cocone)) := by
  sorry
  -- use a lemma in mathlib : cofinal colimit iso ?

inductive overYonedaArrows (F : Cᵒᵖ ⥤ Type max u v) :
    (G : Cᵒᵖ ⥤ Type max u v) → (G ⟶ colimit (overYoneda'.{u, v, max u v} F)) → Prop where
  | of (Y : C) (s : F.obj (op Y)) : overYonedaArrows F (CategoryTheory.uliftYoneda.obj Y)
      (colimit.ι (overYoneda'.{u, v, max u v} F) ⟨op Y, s⟩)

theorem fnejzi (F : Sheaf (Sheaf.canonicalTopology (Sheaf J C)) (Type max u v)) :
      IsRepresentable F.val := by
    -- have e := natIsoColimitOverYoneda'.{u, v, max u v} F.val
    let S : Presieve (colimit (overYoneda'.{u, v, max u v} F.val)) :=
      fun Y => { f | overYonedaArrows F.val Y f }

    have : (Limits.colimit (overYoneda'.{u, v, max u v} F.val)).IsRepresentable := by
      sorry
      -- suffices Nonempty (Limits.IsColimit ()) by
      --  sorry
    exact isRepresentable_of_natIso' (Limits.colimit (overYoneda'.{u, v, max u v} F.val)) e.symm

/- section

open Limits

variable (F : Sheaf J (Type max u v))

def homEquivOverCompSections (G : Sheaf J (Type max u v)) :
    (F ⟶ G) ≃ (sectionOver.over F.val ⋙ G.val).sections where
  toFun α := ⟨
      fun s => α.val.app s.fst s.snd,
      fun {s s'} f => by
        change (α.val.app s.fst ≫ G.val.map f.fst) s.snd = α.val.app s'.fst s'.snd
        rw [← α.val.naturality]
        simp
    ⟩
  invFun σ := Sheaf.Hom.mk {
      app X x := σ.val (⟨X, x⟩ : sectionOver F.val),
      naturality {X Y} f := by
        ext x
        simp only [types_comp_apply,
          ← σ.prop ({ fst := f } : sectionOverMorphism F.val ⟨X, x⟩ ⟨Y, F.val.map f x⟩)]
        rfl
    }
  left_inv _ := rfl
  right_inv _ := rfl

def coyonedaObjIso :
    coyoneda.obj (Opposite.op F) ≅
      sheafToPresheaf J (Type max u v) ⋙ coyoneda.obj (Opposite.op F.val) :=
  NatIso.ofComponents (fun _ => (fullyFaithfulSheafToPresheaf J (Type max u v)).homEquiv.toIso)

noncomputable def coyonedaOpNatIsoWhiskeringLeftOverCompLim :
    coyoneda.obj (Opposite.op F) ≅
      sheafToPresheaf J _ ⋙ (whiskeringLeftOver F.val) ⋙ lim :=
  (coyonedaObjIso J F) ≪≫ isoWhiskerLeft _ (coyonedaOpNatIsoWhiskeringLeftOverCompLim' F.val)

def uliftFunctorIsoId : uliftFunctor.{u, max u v} ≅ .id (Type max u v) :=
  NatIso.ofComponents (fun X => Equiv.ulift.toIso)

@[simps]
def overYoneda : (sectionOver F.val)ᵒᵖ ⥤ (Sheaf J (Type max u v)) where
  obj s := J.uliftYoneda.obj s.unop.fst.unop
  map f := J.uliftYoneda.map f.unop.fst.unop

def overCompYonedaCompCoyonedaFlipNatIsoWhiskeringLeftOver :
    (sectionOver.over F.val ⋙ J.uliftYoneda.op ⋙ coyoneda).flip
      ≅ sheafToPresheaf J _ ⋙ (whiskeringLeftOver F.val) :=
  (flipFunctor _ _ _).mapIso (isoWhiskerLeft (sectionOver.over F.val)
    (J.largeCurriedUliftYonedaLemma ≪≫ isoWhiskerLeft (evaluation _ _)
      (isoWhiskerRight ((whiskeringRight _ _ _).mapIso uliftFunctorIsoId)
        ((whiskeringLeft _ _ _).obj _) ≪≫ (Iso.refl _))))

#check J.overYoneda F

instance : HasColimitsOfSize (Sheaf J (Type max u v)) :=
  Sheaf.instHasColimitsOfSize

noncomputable def coyonedaOpColimitOverYonedaNatIsoWhiskeringLeftOverLim :
    coyoneda.obj (Opposite.op (colimit (J.overYoneda F))) ≅
      sheafToPresheaf J _ ⋙ (whiskeringLeftOver F) ⋙ lim :=
  (coyonedaOpColimitIsoLimitCoyoneda' (overYoneda F)).trans
    ((limitIsoFlipCompLim _).trans
    (isoWhiskerRight (J.overCompYonedaCompCoyonedaFlipNatIsoWhiskeringLeftOver F) _))

theorem fnejzi (F : Sheaf (Sheaf.canonicalTopology C) (Type max u v)) : IsRepresentable F.val := by
    #check natIsoColimitOverYoneda'.{u, v, max u v} F.val
    sorry

end -/

end CategoryTheory.GrothendieckTopology
