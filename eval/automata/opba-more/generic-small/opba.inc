opa:  initials = 0;
      finals = (4 10);
      deltaPush =
        (0,  (call pa),   1),
        (1,  (han),       2),
        (2,  (call pb),   3),
        (3,  (call pc),   4),
        (4,  (call pc),   4),
        (6,  (call perr), 7),
        (8,  (call perr), 7),
        (10, (call),     10);
      deltaShift =
        (4, (exc),       5),
        (7, (ret perr),  7),
        (9, (ret pa),   11),
        (10, (ret),     10);
      deltaPop =
        (4, 2, 4),
        (4, 3, 4),
        (4, 4, 4),
        (5, 1, 6),
        (7, 6, 8),
        (7, 8, 9),
        (11, 0, 10),
        (10, 10, 10);