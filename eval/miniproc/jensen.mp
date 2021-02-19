var P_cp, P_db, P_rd, P_wr, CP;

main() {
  P_cp = true;
  P_db = true;
  P_rd = true;
  P_wr = true;
  CP = false;
  spender();

  P_cp = false;
  P_db = false;
  P_rd = false;
  P_wr = false;
  clyde();
}

spender() {
  account.canpay();
  if (P_cp) {
    account.debit();
  } else {}

  if (*) {
    spender();
  } else {}
}

clyde() {
  account.debit();
  if (*) {
    clyde();
  } else {}
}

account.canpay() {
  if (P_cp) {
    read();
    CP = true;
  } else {
    throw;
  }
}

account.debit() {
  if (P_db) {
    account.canpay();
    if (CP) {
      write();
      CP = false;
    } else {
      throw;
    }
  } else {
    throw;
  }
}

read() {
  if (P_rd) {
    raw_read();
  } else {
    throw;
  }
}

write() {
  if (P_wr) {
    raw_write();
  } else {
    throw;
  }
}

raw_read() {}
raw_write() {}
