---
name: backup-progress
description: Save current proof progress to CLAUDE.md, memory files, and optionally commit. Use periodically during long sessions or after completing a proof milestone.
user-invocable: true
allowed-tools: Read, Write, Edit, Bash, Grep, Glob
effort: medium
---

## Backup Session Progress

Save the current state of work to persistent storage so it survives session crashes.

### Checkpoint frequency

- **Every ~15 minutes** during active proof work
- **Immediately** after completing a lemma or theorem (removing a sorry)
- **Immediately** after discovering a dead end or key insight
- **Immediately** after the user corrects the strategy or approach
- **Before** attempting a risky refactor

You should proactively call `/backup-progress` at these intervals without being asked. If you notice you haven't checkpointed in a while, do it.

### Steps

1. **Check current proof state**: Read modified Lean files and identify what has changed since last checkpoint
2. **Update CLAUDE.md**:
   - Update the "Status" section with current sorry count and what's done
   - Add any new "Learned reasoning patterns" discovered this session
   - Add any new "Debugging lessons" encountered
   - Update the "Current goal" section if the strategy has evolved
3. **Update memory files**: Write/update memory files in `~/.claude/projects/-home-anqi-compositional-protocol-proof/memory/` for cross-session knowledge
4. **Report**: Summarize what was backed up and when the next checkpoint should happen

### What to capture

- Which theorems/lemmas are proven vs sorry'd
- Proof approaches that worked or failed (and WHY they failed)
- Key insights about definitions or structure discovered during this session
- Any corrections from the user about strategy or approach
- Dead ends to avoid in future sessions

### Constraints

- Do NOT commit to git unless explicitly asked
- Do NOT modify proof code — this is documentation-only
- Keep CLAUDE.md concise — it must remain readable
