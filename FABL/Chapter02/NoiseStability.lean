/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter02.NoiseStability.NoiseKernels
public import FABL.Chapter02.NoiseStability.CorrelatedGaussianLimit
public import FABL.Chapter02.NoiseStability.GaussianDisagreement
public import FABL.Chapter02.NoiseStability.NoiseOperator
public import FABL.Chapter02.NoiseStability.FourierFormulas
public import FABL.Chapter02.NoiseStability.StableInfluence

/-!
# Noise stability

Book coverage: Section 2.4.

Formalization of Section 2.4 of O'Donnell's *Analysis of Boolean Functions*, including the
two-dimensional central-limit and Gaussian-angle proof of Theorem 2.45 supplied in Chapter 5.2.
-/
