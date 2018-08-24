### Version 0.0.1 -- Technical Preview

It works correctly.

There are many implementation alternatives:
- 'clauses' and 'learnt' databases, which contain clause data. And Watcher and 'reason' holds a clause ID.
- a single clause database holds clause data. And Watcher and 'reason' hold a clause ID.
- A single clause database holds clause data. Watcher is embedded into the database.

After some comparisons, I selected the last one due to the performance.
