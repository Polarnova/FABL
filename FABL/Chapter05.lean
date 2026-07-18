/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import FABL.Chapter05.LinearThresholdFunctions
import FABL.Chapter05.SparsePolynomialApproximation
import FABL.Chapter05.DNFSparsePolynomialThreshold
import FABL.Chapter05.IntegralThresholdRepresentations
import FABL.Chapter05.ChowTheorem
import FABL.Chapter05.ThresholdFunctionCounting
import FABL.Chapter05.InnerProductModTwo
import FABL.Chapter05.BerryEsseenConsequences
import FABL.Chapter05.BerryEsseenIntervals
import FABL.Chapter05.BerryEsseenRescaling
import FABL.Chapter05.RademacherFirstMoment
import FABL.Chapter05.LevelOneInequality
import FABL.Chapter05.SharpLevelOneInequality
import FABL.Chapter05.NearlyConstantLevelOne
import FABL.Chapter05.SmallSetCenterOfMass
import FABL.Chapter05.CorrelatedMajority
import FABL.Chapter05.CorrelationDistillation
import FABL.Chapter05.RandomBooleanFourierMaximum
import FABL.Chapter05.RegularThresholdNoiseStability
import FABL.Chapter05.FourierCoefficientsOfMajority
import FABL.Chapter05.KrawtchoukPolynomials
import FABL.Chapter05.MajorityComplementaryWeights
import FABL.Chapter05.MajorityWeightMonotonicity
import FABL.Chapter05.MajorityNoiseStability
import FABL.Chapter05.MajorityLargestFourierCoefficient
import FABL.Chapter05.MajorityFourierOneNorm
import FABL.Chapter05.MajorityLimits
import FABL.Chapter05.LimitingMajorityWeights
import FABL.Chapter05.MajorityFourierWeightLimits
import FABL.Chapter05.MajorityFourierWeightRecovery
import FABL.Chapter05.MajorityFourierTailAsymptotics
import FABL.Chapter05.KhintchineKahane
import FABL.Chapter05.LinearThresholdLevelOne
import FABL.Chapter05.LinearThresholdInfluence
import FABL.Chapter05.DegreeOneWeight
import FABL.Chapter05.TwoDivPi
import FABL.Chapter05.GaussianIsoperimetric
import FABL.Chapter05.GaussianIsoperimetricConcavity
import FABL.Chapter05.GaussianMillsRatio
import FABL.Chapter05.GaussianIsoperimetricAsymptotics
import FABL.Chapter05.GaussianSharpLevelOne
import FABL.Chapter05.GaussianSharpLevelOneCounterexample
import FABL.Chapter05.GaussianThresholds
import FABL.Chapter05.GotsmanLinialExtremizer
import FABL.Chapter05.HammingBallLimit
import FABL.Chapter05.BiasedMajorityGaussianLimit
import FABL.Chapter05.FKNImprovement
import FABL.Chapter05.ImprovedFKN
import FABL.Chapter05.FKNOptimality
import FABL.Chapter05.UnateFunctions
import FABL.Chapter05.AverageInfluence
import FABL.Chapter05.UniformNoiseStability
import FABL.Chapter05.RobustEdgeIsoperimetry
import FABL.Chapter05.Peres
import FABL.Chapter05.LTFNoiseSensitivityDerivative
import FABL.Chapter05.PolynomialThresholdUniformStability
import FABL.Chapter05.PolynomialThresholdInfluence
import FABL.Chapter05.LinearThresholdBias
import FABL.Chapter05.ParityThresholdDegree
import FABL.Chapter05.SmallLowDegreeWeightPTF
import FABL.Chapter05.ThresholdCircuits
import FABL.Chapter05.AC0ThresholdParitySeparation
import FABL.Chapter05.PrescribedFourierSupport

/-!
# Chapter 5: Majority and threshold functions

Chapter 5 is complete. Every result proved within the chapter's formalization boundary is associated
with compiled production declarations. Open conjectures, external results, and arguments deferred
by the book to later chapters remain explicit statement-only Blueprint nodes.

This file is the public import surface for Chapter 5.
-/
