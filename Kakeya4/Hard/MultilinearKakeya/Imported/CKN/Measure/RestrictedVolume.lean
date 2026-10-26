/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
/- Adapted from LeanPool/lean-pool pin 7d5e94f7172d47c78cac7f23c0dd01cef1665e42.
Original module: LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Measure.RestrictedVolume.
Changes: project-local import paths and this provenance comment only.
The mathematical declarations and proofs are unchanged. Full LICENSE and NOTICE accompany this directory. -/

module

public import Kakeya4.Hard.MultilinearKakeya.Imported.CKN.Ambient.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Restricted Lebesgue volume

Adapted from PDEFoundation (EllipticRegularity, 2026) with the author's
permission. This port keeps the common restricted-volume abbreviations and
drops domain regularity predicates that are not needed by weak derivatives.
-/

@[expose] public section

namespace CKN

/-- Lebesgue volume restricted to a native-vector domain. -/
noncomputable abbrev volumeOn {d : ℕ} (U : Set (Vec d)) :=
  MeasureTheory.volume.restrict U

/-- Compatibility name for the restricted volume measure. -/
noncomputable abbrev volumeMeasureOn {d : ℕ} (U : Set (Vec d)) :=
  volumeOn U

end CKN

