# Project 0: Template

Copyright (c) 2026 Frankie Feng-Cheng WANG. All rights reserved. Repository: https://github.com/FrankieeW/formalising-mathematics-notes

This folder provides a blank Lean + TeX template for starting a new project.

## Overview

- Use `Main.lean` for the core formalisation.
- Use `Test.lean` for scratch work.
- Use `Report/report.tex` for the write-up.

## Files

- `Main.lean` main Lean entry point.
- `Test.lean` scratch space.
- `Report/report.tex` report template.
- `Report/checklist.md` blank checklist.
- `Report/references.bib` bibliography placeholder.

## Prerequisites

- Lean 4 with mathlib (see the repo root for setup).
- Run `lake exe cache get` once after cloning to download the mathlib cache.

## How to check the project

From the repository root:

```bash
lake env lean Project0/Main.lean
```
