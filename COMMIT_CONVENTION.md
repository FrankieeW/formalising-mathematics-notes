# Git Commit Message Convention

## Format

```
<type>(<scope>): <subject>

[optional body]

[optional footer]
```

## Commit Types

| Type | Description | Example |
|------|-------------|---------|
| `feat` | New feature or content | `feat(Project1): add stabilizer subgroup proof` |
| `fix` | Bug fix or proof completion | `fix(Section05/Sheet1): complete group axioms proofs` |
| `docs` | Documentation changes | `docs(Project1): improve report introduction` |
| `style` | Formatting changes (no logic change) | `style(report): optimize Lean code indentation` |
| `refactor` | Code refactoring | `refactor(Project1): rename to snake_case convention` |
| `test` | Adding tests | `test(Section04): add set theory test cases` |
| `chore` | Build, tools, or configuration changes | `chore: update lakefile dependencies` |

## Scope

Recommended scopes for this project:
- `Project0`, `Project1` - Project-related changes
- `Section01`, `Section05` - Course section changes
- `Sheet1`, `Sheet3` - Exercise sheet changes
- `report` - Report documentation
- `Main` - Main file changes

## Subject Guidelines

- Use imperative mood (verb base form): "add", "fix", "improve"
- Do not capitalize the first letter (unless proper noun)
- No period at the end
- Limit to 50 characters

## Examples

### ✅ Good Examples

```
feat(Project1): add permutation representation proof

- Define sigma and sigmaPerm functions
- Prove phi_mul and phi_one lemmas
- Complete group_action_to_perm_representation theorem
```

```
style(report): optimize Lean code indentation

- Remove all leading tabs from leancode blocks
- Apply consistent 2-space indentation
- Verify LaTeX compilation successful
```

```
fix(Section05/Sheet1): complete group closure proofs

Completed exercises:
- Group.one_mul proof
- Group.mul_assoc verification
- Group.inv_mul proof
```

### ❌ Bad Examples

```
Update files  # Too vague
```

```
Project1 Commit Message: 0121  # Unclear
```

```
Add some stuff to the report and fix things  # Not specific
```

## Special Cases

### Amending a Commit

To modify the most recent commit message:

```bash
git commit --amend -m "new message"
```

### Multi-file Commits

When multiple files are involved, list them in the body:

```
feat(Project1): complete group action theory

Modified files:
- Main.lean: add GroupAction instances
- Report/report.tex: document mathematical proofs
- Test.lean: add verification examples
```

## Project-Specific Guidelines

Based on this project's nature:
1. Use `feat` or `fix` for Lean code submissions
2. Use `docs` or `style` for report documentation
3. Use `chore` for configuration files
4. Use `refactor` for code restructuring

## Tools

Optional: Install commitizen for interactive commit messages:
```bash
npm install -g commitizen
commitizen init cz-conventional-changelog --save-dev --save-exact
```

Then use `git cz` instead of `git commit`
