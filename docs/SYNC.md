# Automatic repository sync

The maintainer has authorized publishing completed project changes to `main`.
Agents pull before work and commit/push after completing the relevant checks.
A daily Codex task also checks the local clone for changes. That local task
requires the computer to be on, the desktop app running, and repository access.
It is configured in the maintainer's app, not installed by cloning this repo.

The sync task does Git maintenance only. It does not authorize additional RH
research outside the separately configured research window, consume paid
credits, or change the mathematical verification requirements.

## Procedure

1. Confirm the expected repository, `origin`, and `main` branch. If another
   worker is editing, the index already contains staged work, a Git lock exists,
   or a merge/rebase is in progress, defer the sync.
2. Fetch `origin`. Inspect local changes, including new files, for intended
   public project content. Exclude ignored files, secrets, private logs,
   downloaded dependencies, and unfinished work. Stage reviewed paths
   explicitly; do not blindly stage the entire directory.
3. Run checks appropriate to changed code, review the staged diff, and commit
   completed changes with a descriptive message. Do not manufacture a commit
   when nothing changed. If changes cannot be safely classified, leave them
   intact and report them.
4. With a clean working tree, integrate `origin/main`. Prefer
   `git merge --ff-only origin/main` when possible. If both branches advanced,
   a normal `git merge --no-edit origin/main` is permitted. If it conflicts,
   abort that merge, preserve the local commits, and report the conflicting
   files. Do not automatically resolve conflicts, reset files, or force-push.
5. Check changes introduced by a merge as appropriate, then run
   `git push origin main`. If the push is rejected because a collaborator
   pushed meanwhile, fetch and retry integration once; otherwise report the
   blocker. Verify local `HEAD` matches the fetched remote branch afterward.

Never push when checks fail, the working tree contains unrelated unfinished
changes, the branch/remote is unexpected, or authentication fails. Preserve the
work and report what needs attention. Do not automatically start hosted Actions;
the existing verification workflow is manual.
