# A five-minute fresh-reader check

Status: **Pending a real reader.** Automated arithmetic and browser checks do not establish whether the explanation makes sense to someone seeing it for the first time.

Invite one curious reader who has not discussed the project with us. Start at <https://reptends.mikedotexe.com/> on their usual device. Do not explain the mathematics first. Ask them to read and use the page at their own pace for about five minutes, saying aloud what they notice if they are comfortable doing so.

Tell them: “We are checking how clearly the page explains itself. You are not being tested. If something is confusing, that is useful information for us.”

After they have explored, ask these questions without offering hints or correcting the first response:

1. What surprised you, or made you want to keep reading?
2. Where does the extra 2 in 729 → 731 come from?
3. When the page says a cycle returns, what exactly repeats? What keeps growing?
4. If we add more nines to the denominator, what changes about the groups of digits and the pattern we can see?
5. When we reach the last digit of the repeating block, do the powers stop? What have we learned at that point?
6. Where did you feel lost, and what would you try clicking next?

If they explored the optional geometry, add: “What are we gathering along a diagonal or into a triangular slice? Is gathering those contributions the same as carrying?” Skip this question if they did not reach that section.

Record their own words before discussing the intended explanation. A wrong answer is a clue about the page, not a score. Do not substitute a model-generated answer or an author's interpretation for an actual reader's response.

## Session record

- Date and page version/commit: _pending_
- Reader's preferred anonymous label: _pending_
- Device and browser: _pending_
- Prior comfort with long division: _pending_
- Sections and controls they actually used: _pending_
- Response 1, in their words: _pending_
- Response 2, in their words: _pending_
- Response 3, in their words: _pending_
- Response 4, in their words: _pending_
- Response 5, in their words: _pending_
- Response 6, in their words: _pending_
- Optional geometry response: _not asked / pending_
- Observed pauses, misclicks, or inaccessible controls: _pending_
- One change supported by this session: _pending_

## Debrief notes for the facilitator

Read this only after recording the initial responses. At the seventh group, all later terms together contribute 2187/997 = 2 + 193/997 in that group's units; the whole 2 changes 729 to 731. The remainder and printed group return after 166 three-digit steps while the unbounded power grows. Those steps span 498 decimal positions, containing three copies of the minimal 166-digit decimal period. The first decimal return for 1/997 falls inside group 56, associated with 3^55; it gives a finite description of the digits without truncating the infinite power series. Increasing the fixed decimal grouping width (using denominators such as 997 and 9997, which are 3 below 1000 and 10000) exposes more powers of three before carrying alters their printed groups. Collecting square/cube contributions gives coefficients; carrying subsequently settles them into fixed-width groups.

Keep the response notes anonymous unless the reader explicitly wants credit. Discussing the result together afterward is encouraged; label any later revised answer separately from the initial response.

## Separate AI review — 8 October 2026, v1.1.0

Three agents independently read the published essay without the author discussion history, followed the main path before opening optional explanations, and tried the live controls. These are AI reviews; the human session record above remains pending. The reviewers were mathematically informed and should not be treated as novice participants.

All three correctly described the carry contribution, growing powers versus repeating remainders, the effect of added nines, and the non-termination of the powers before opening optional mathematics. All three identified visual difficulty separating the opening digit groups, an implicit step connecting powers to division remainders, and loss of the `7 | 00` boundary after clicking “Inspect the decimal return.” One asked why omitted rows cannot change the table's completed columns; the finite-prefix guide resolved that question. They consistently valued the 729→731 puzzle followed by aligned addition and the cycle-return control.

The v1.1.1 clarification pass addresses these findings while preserving the main chapter structure. A real reader's responses should be recorded independently, without being coached using this review.
