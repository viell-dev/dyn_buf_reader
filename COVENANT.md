# FOSS Covenant

This document is a commitment by the Maintainer of `DynBufReader` about how
the Project will be licensed over time. It exists to reassure contributors
and users that the sublicensing power granted in [CLA.md](CLA.md) is meant
for the alternative license grants described in
[ALTERNATIVE-LICENSE.md](ALTERNATIVE-LICENSE.md), and not as a route for the
Project to become non-FOSS at some point in the future.

This document is not legal advice. Like the CLA, it is intended to be read
and relied on in plain English.

## Definitions

"Project" has the same meaning as in [CLA.md](CLA.md): the `DynBufReader`
project and related repositories, releases, and distributions maintained by
the Maintainer.

"Maintainer" has the same meaning as in [CLA.md](CLA.md): the person or
persons who, at a given point in time, control the canonical source
repository and public releases of the Project, together with any successor
or assignee of those rights. The Maintainer may be a single individual, a
group of co-maintainers acting jointly, or a successor entity that later
acquires those rights; in every case, the commitments in this covenant
apply to whoever holds that role at the time, and bind them for the period
during which they hold it.

When this document says "the Maintainer commits" or "the Maintainer will
not," it means the current Maintainer at the time of the action in
question, acting in that capacity. Co-maintainers are bound jointly: no
subset of co-maintainers may take an action inconsistent with this covenant
on the grounds that the others did not participate.

## Why this exists

The CLA gives the Maintainer broad rights over each Contribution, including
the right to sublicense it under alternative terms. That power is load-bearing
for [ALTERNATIVE-LICENSE.md](ALTERNATIVE-LICENSE.md): without it, the
Maintainer could not offer narrowly-scoped non-FOSS grants to Licensees who
cannot use the public release under `GPL-3.0-only`.

The same power would, in principle, also allow the Maintainer to simply
relicense the canonical Project under proprietary terms and stop releasing it
as Free Software. That is not the intention, it has never been the intention,
and this document is how the Maintainer says so in writing.

Contributors should be able to submit work to `DynBufReader` knowing that the
public release will stay FOSS. Users and downstream distributors should be
able to depend on the Project without worrying that a future canonical
release will be proprietary-only. This covenant is the Maintainer's binding
promise that both of those expectations will hold.

## 1. Scope

This covenant applies to the **canonical Project** — the source repository,
releases, and distributions under the Maintainer's control, as defined in
[CLA.md](CLA.md). It binds the Maintainer and any successor or assignee of
the Maintainer's rights in the Project. Anyone who acquires those rights
acquires them subject to this covenant.

It does **not** restrict what third parties do with their own forks or
derivative works under the Public License. Third parties are free to do
whatever the Public License allows, including maintaining forks under
`GPL-3.0-only`. This covenant only constrains the Maintainer.

## 2. The public release stays FOSS

The Maintainer commits that every public release of the Project will be
distributed under a **FOSS license** — specifically, a license that is:

- approved by the Open Source Initiative as an Open Source license; **and**
- a strong copyleft license in the GPL family, or a successor to it of
  comparable character.

As of this covenant, that license is `GPL-3.0-only` together with the
Universal FOSS Exception, Version 1.0 (see
[LICENSE-EXCEPTION.md](LICENSE-EXCEPTION.md)), and the Maintainer's intent is
to stay on `GPL-3.0-only` for the foreseeable future. The Maintainer has
deliberately chosen `GPL-3.0-only` rather than `GPL-3.0-or-later` so that
future GPL versions do not automatically apply to the Project sight unseen.

The Maintainer may move the Project to a different license satisfying the
conditions above — for example, to a future `GPL-4.0-only` if and when such
a license exists and the Maintainer is satisfied with its terms, or to
another strong-copyleft FOSS license in comparable spirit — but any such
move must itself produce a FOSS release under this section. The Project's
canonical release will never be made proprietary, source-available-only,
shared-source, "business source," time-delayed, non-commercial-only, or
otherwise non-FOSS.

If a future license change is ever made, this document will be updated in
the same commit, and the rationale recorded in the commit message or an
accompanying note, so the history of the covenant is visible in the
repository.

## 3. Alternative grants are additional, never a replacement

The alternative license grants described in
[ALTERNATIVE-LICENSE.md](ALTERNATIVE-LICENSE.md) are **additional
permissions** offered to specific Licensees for specific Approved Uses.
They exist alongside the public FOSS release; they do not replace it, carve
it up, or reduce it.

The Maintainer commits that:

- every version of the Project that is released at all will be released
  publicly under the Public License described in Section 2, in the normal
  way, at the same time as or before it is made available to any
  alternative-grant Licensee;
- alternative grants will only ever be offered on top of a public FOSS
  release, not instead of one;
- the Maintainer will not maintain a private, proprietary-only fork of the
  canonical Project that is withheld from the public release. Ordinary
  pre-release branches, work-in-progress, and unreleased code do not count
  as a "private fork" for this purpose, as long as they are intended to
  land in a public FOSS release in the normal course of development; and
- the Maintainer will not use the CLA's sublicensing power to relicense the
  canonical Project under terms that would let a third party take it
  non-FOSS, or to transfer the Project to anyone who has not agreed to be
  bound by this covenant.

## 4. Relationship to the CLA

This covenant sits on top of [CLA.md](CLA.md) and narrows how the Maintainer
will exercise the rights granted there. It does not change what Contributors
grant under the CLA, and it does not give Contributors any new rights in
their Contributions beyond what they already retain under CLA § 2.

In the event of a conflict between this covenant and the CLA, the covenant
controls the Maintainer's conduct — that is, the CLA describes what the
Maintainer **may** do as a matter of copyright, and this covenant describes
what the Maintainer **will** do as a matter of commitment.

## 5. Durability

This covenant is intended to be durable. The Maintainer may update it to
clarify wording, correct errors, or reflect a license change permitted by
Section 2, but may not amend it in a way that weakens the core commitments
in Sections 2 and 3 — namely, that the canonical Project's public release
stays under a strong-copyleft FOSS license, and that alternative grants
remain additional to that public release rather than a replacement for it.

Any successor or assignee of the Maintainer's rights in the Project takes
those rights subject to this covenant, and by accepting them agrees to be
bound by it on the same terms.
