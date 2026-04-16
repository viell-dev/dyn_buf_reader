# Alternative License Grant (Draft Template)

> This document is a **draft template** for an alternative license grant that
> `DynBufReader`'s maintainer may offer on request. It is not a grant by
> itself — no rights exist until both parties sign a separate written
> agreement that incorporates (or replaces) these terms.
>
> It is intended as a practical starting point, not legal advice. Have a
> lawyer review it for your jurisdiction before relying on it.

## Why this exists

`DynBufReader` is distributed publicly under `AGPL-3.0-only`. An alternative
license grant is for the case the public license does **not** cover: somebody
wants to use `DynBufReader` inside a closed-source, proprietary, or otherwise
non-FOSS product or service, and therefore cannot comply with `AGPL-3.0-only`.

The maintainer's default disposition is:

- **Non-commercial, hobbyist, or non-profit proprietary use** — granted on
  request, at no charge.
- **Small and mid-sized commercial use** — also granted on request, at no
  charge by default. The goal is to be helpful, not to squeeze.
- **Large commercial use** — still granted on request, but the Maintainer may
  ask the Licensee to reciprocate with a small one-off contribution to the
  project. The point is not a price tag; it is that handing a free favor to
  an organization that could trivially support its upstreams, and won't,
  isn't really a favor worth doing. The size of the ask scales with how
  obvious the answer is, and is always open to conversation.

In all cases, the grant is a one-off favor tied to a specific licensee and a
specific use. It is not a product, and the Maintainer is not trying to run a
business around it — but the Maintainer also reserves normal judgment about
which favors are worth doing, the same way anyone would.

## Template terms

The terms below describe the default shape of a grant. The signed agreement
may broaden, narrow, or replace any of them.

### 1. Parties

- **Maintainer:** `[Maintainer legal name]`, copyright holder of `DynBufReader`,
  together with any successor or assignee of the project rights.
- **Licensee:** the legal person or entity identified in the signed agreement.

### 2. Definitions

- **"Project"** means `DynBufReader`, including all versions released by the
  Maintainer under the public license, both existing as of the effective date
  and released afterwards.
- **"Approved Use"** means the single product, service, or internal project
  identified in the signed agreement, together with its successor versions,
  rebrandings, and ordinary internal tooling that exists to build, test,
  operate, or support it. The signed agreement must describe the Approved
  Use specifically enough that a reasonable reader can tell what is in scope
  and what is not — for example, a named product line, a named service, or a
  named internal system, rather than a broad problem domain. The Approved
  Use is not a license to use the Project across Licensee's unrelated
  products, unrelated services, or unrelated internal projects; each of
  those would need its own grant.
- **"Public License"** means `AGPL-3.0-only`, as the Project is distributed
  publicly.

### 3. Grant

Subject to the conditions below, the Maintainer grants Licensee a perpetual,
worldwide, non-exclusive, royalty-free (unless a fee is separately agreed)
license to:

- use, reproduce, modify, and prepare derivative works of the Project;
- incorporate the Project (in source or object form) into the Approved Use;
- distribute the Project as an embedded component of the Approved Use, in
  source or object form, to customers, users, and other recipients of the
  Approved Use;

without being required to comply with `AGPL-3.0-only` with respect to the
Approved Use, and without being required to license the Approved Use itself
under `AGPL-3.0-only`.

The grant covers the Project as released by the Maintainer over time.
Licensee is free to update to newer public releases of the Project under this
same grant. Licensee is not required to re-request a license for each new
version.

### 4. What the Licensee may not do

Licensee may not:

- sublicense, transfer, or assign this grant, in whole or in part, to any
  other person or entity. Changes of control of the Licensee (merger,
  acquisition, sale of the business relating to the Approved Use, or similar)
  are handled under Section 12;
- use this grant as a basis to relicense, redistribute, or offer the Project
  to third parties under terms other than the Public License. Third parties
  who obtain the Project indirectly through the Approved Use do so under the
  **Public License**, which they remain free to rely on. Third parties who
  want their own non-FOSS rights must request their own grant;
- extend this grant to unrelated products, services, or internal projects not
  named as the Approved Use, without a further written agreement;
- remove or obscure copyright, license, or attribution notices that appear in
  the Project's source or bundled documentation.

### 5. What the Licensee may do

Licensee may:

- modify the Project for the Approved Use, and keep those modifications
  private;
- distribute the Project in object form as an embedded component of the
  Approved Use;
- distribute the Project in source form as part of the Approved Use's own
  source distribution, if any, provided the Project's notices are preserved;
- allow employees, contractors, affiliates, and agents acting on Licensee's
  behalf to exercise the rights in this grant for the Approved Use.

### 6. Public License unaffected

Nothing in this grant reduces or overrides any rights a recipient may have
under a separately obtained copy of the Project under the Public License.
Anyone who has a copy of the Project through the public release continues to
hold the rights the Public License gives them, regardless of this grant.

This grant is an **additional** permission to Licensee. It does not replace,
rescind, or modify the Public License as it applies to anyone else.

### 7. Patent grant and termination

The Maintainer grants Licensee a non-exclusive, worldwide, royalty-free
license under patent claims the Maintainer owns or controls that would
necessarily be infringed by the Project as distributed, to make, use, sell,
offer for sale, import, and distribute the Project as part of the Approved
Use.

If Licensee (or any entity on whose behalf Licensee acts) institutes patent
litigation against the Maintainer or any other user of the Project alleging
that the Project, or a contribution incorporated into it, directly or
indirectly infringes a patent, then this grant terminates automatically as of
the filing date of that litigation.

### 8. Public record

The Maintainer keeps a public record of alternative license grants in
[GRANTS.md](GRANTS.md). The purpose of the record is transparency: anyone
reading the project can see how many non-FOSS grants exist and, where the
Licensees have agreed, who holds them.

Each grant is assigned a unique, sequential **grant number** when it is
issued, and that grant number is referenced in the signed agreement.
Grant numbers are permanent and do not change if the Licensee later
changes their listing preference, if the grant moves between active and
expired status, or if it is continued under a new controlling entity
after a change of control.

Licensee consents to the existence of the record, and chooses at request
time how this grant should appear in it. The options are:

- **by name**, identifying Licensee and the Approved Use;
- **by category only**, using a generic label such as *"A non-profit
  organization"* or *"A commercial company (undisclosed)"*, without naming
  Licensee or the Approved Use; or
- **not listed**, in which case the grant is counted in the aggregate
  undisclosed count in [GRANTS.md](GRANTS.md) but does not appear as an
  entry.

The default, if Licensee expresses no preference, is **category only**.
Licensee may change the preference at any time by writing to the
Maintainer; the Maintainer will update [GRANTS.md](GRANTS.md) within a
reasonable time of receiving the request.

The public record is informational. It does not create, modify, or replace
the rights granted under this grant, and a discrepancy between the record
and the signed agreement is resolved in favor of the signed agreement.

### 9. Trademarks

This grant does not give Licensee any right to use the name `DynBufReader`,
the Maintainer's name, or any related trademark or trade name, except for
factual, descriptive references ("uses `DynBufReader`" and similar).

### 10. No warranty

The Project is provided "as is," without warranty of any kind, express or
implied, including warranties of merchantability, fitness for a particular
purpose, and non-infringement. The Maintainer is not liable for any damages
arising from Licensee's use of the Project under this grant, to the fullest
extent permitted by applicable law.

### 11. Term and termination

This grant is perpetual with respect to versions of the Project released on
or before any termination date.

The Maintainer may terminate this grant for material breach of Sections 4,
7, 9, or 12 on 30 days' written notice, if the breach has not been cured
in that period. Termination does not affect any version of the Approved Use
already distributed by Licensee before the termination date, which may
continue to be supported and serviced using the Project versions covered
before termination.

### 12. Change of control

If Licensee undergoes a change of control — including merger, acquisition,
sale of all or substantially all of the business relating to the Approved
Use, or any transaction in which a different entity comes to direct or
indirectly control Licensee — the grant does **not** automatically pass to
the new controlling entity.

Licensee must give the Maintainer written notice of the change of control
within 30 days of it closing (or, if notice before closing is legally
permitted and practical, before closing).

The Maintainer then has 60 days from receiving that notice to:

- **confirm** that the grant continues under the new controlling entity,
  unchanged, with the new entity stepping into Licensee's position; or
- **propose amended terms** (for example, a one-off contribution of the kind
  described in the preamble) as a condition for continuing the grant under
  the new controlling entity; or
- **decline** to continue the grant under the new controlling entity, in
  which case the grant terminates with respect to future conduct on the
  terms below.

If the Maintainer neither declines nor proposes amendments within that
60-day window, the grant is deemed confirmed under the new controlling
entity. The 60-day clock only runs from the moment the Maintainer has
actually received written notice under this section; it does not run while
Licensee is in breach of the notice obligation.

If the Maintainer declines, or if the parties cannot agree on amended terms
within a further 60 days, the grant terminates as to any conduct of the
Licensee (and the new controlling entity) after the end of that period, but:

- any copies of the Approved Use already distributed to end users or
  customers before termination may continue to be used, supported, and
  serviced by Licensee and its customers indefinitely under the grant as
  it stood;
- Licensee has a reasonable wind-down period of at least 12 months from the
  termination date to continue distributing and supporting the specific
  major version of the Approved Use that existed at the moment of
  termination, so that in-flight customer commitments are not broken; and
- after the wind-down period, any continued use of the Project in new
  versions of the Approved Use, or in any other Licensee or successor work,
  is governed by the Public License only, unless a new grant is separately
  agreed.

The purpose of this section is practical: the Maintainer grants alternative
licenses as a personal favor based partly on who the Licensee is, and a
change of control is exactly the moment where that judgment may need to be
revisited. It is not intended to punish ordinary corporate reorganizations,
and the Maintainer will not unreasonably withhold continuation for routine
changes that do not materially affect the character of the Licensee.

#### 12.1. Failure to notify

Failure to give the written notice required above within 30 days of the
change of control closing is a material breach of this grant, and any use
of the Project by the new controlling entity during the period of
unremedied breach is outside the scope of the grant and governed by the
Public License only.

If the Maintainer learns of an unnotified change of control from any
source, the Maintainer may:

- treat the change of control as notified on the date the Maintainer
  acquired actual knowledge of it, and exercise the Section 12 review
  rights (confirm, propose amended terms, or decline) as of that date; and
- terminate the grant for material breach under Section 11 on account of
  the missed notice, at the Maintainer's option and without prejudice to
  the Section 12 review.

The Maintainer is not required to choose between those options in advance,
and exercising one does not waive the other. In particular, the Maintainer
may decline continuation under Section 12 **and** terminate for breach
under Section 11 in the same response.

An honest, prompt self-correction — for example, the Licensee realizing
the obligation was missed and writing in voluntarily before the Maintainer
notices — is a factor the Maintainer will consider in good faith when
deciding whether to pursue the breach remedy, but it does not cure the
breach automatically.

### 13. Entire agreement

The signed agreement that incorporates these terms is the entire agreement
between the parties regarding the alternative license grant for the Project.
It does not affect any other agreements between the parties.

## How to request a grant

Requests for an alternative license grant should include:

- the legal name of the requesting person or entity; and
- a short description of the product, service, or internal project that
  would become the Approved Use, specific enough to draw a line around it —
  for example, "the `FooBar` product" rather than "anything we do in the
  FooBar space." If the Licensee isn't sure where the line should fall, a
  rough sketch is fine; the signed agreement is where the final wording
  gets nailed down.

That is usually enough for the Maintainer to decide whether to grant an
alternative license. Commercial organizations are welcome to say a little
about who they are, so the Maintainer has context for the reciprocation
question described above.

Licensees are also encouraged (but not required) to say how they would like
the grant to appear in the public record described in Section 8 and in
[GRANTS.md](GRANTS.md) — **by name**, **by category only**, or **not
listed**. If no preference is stated, the default is **by category only**,
and it can be changed later at any time.

The Maintainer reserves the right to decline any request, for any reason, or
to propose different terms than those in this template.

### What the grant does not include

The alternative license grant allows use of the **public version** of
`DynBufReader` under the template terms above. It is not a support contract
and does not create any obligation on the Maintainer to:

- provide support, maintenance, bug fixes, or security patches;
- produce private builds, private branches, or custom versions;
- release new versions on any particular schedule; or
- respond to Licensee issues on any particular timeline.

The Maintainer will continue to develop `DynBufReader` as a public FOSS
project, and that work will remain available to Licensee under this grant,
but that is the extent of it.
