# Project Agent Instructions

## Quick Reference

```bash
# Analyze codebase and get recommended actions
lazy core ask <target_dir>

# Phase 1 (Vibe Bootstrap): Focus on test discovery
lazy core ask <target_dir> --steps=4

# Phase 2 (Spec Emergence): Bidirectional parity
lazy core ask <target_dir> --steps=1,2,3

# Phase 3 (TDVC Loop): Chase Zero Gap, find implicit bugs, and Vibe More
lazy core ask <target_dir> --steps=1,2,3,4
lazy core ask <target_dir> --steps=5
```

## Interpreting Output

- **URGENT** actions: Execute immediately
- **High** priority: Address in current session
- **Medium/Low**: Queue for later

## Policy Mapping

`lazy core ask` converts gaps → signals → recommendations.
Follow recommendations to maintain project health.
