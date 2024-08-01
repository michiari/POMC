bool P_cp, P_db;
s{width:d} balance;

main() {{
  balance = {initial:d}s{width:d};

  P_cp = true;
  P_db = true;

  spender();

  P_cp = false;
  P_db = false;

  clyde();
}}

spender() {{
  s{width:d} amount;
  bool auth;
  amount = *;

  account.canpay(amount, auth);
  if (auth) {{
    account.debit(amount);
  }} else {{}}
}}

clyde() {{
  s{width:d} amount;
  amount = *;
  account.debit(amount);
}}

account.canpay(s{width:d} amount, bool &auth) {{
  s{width:d} bal;
  if (P_cp) {{
    balance.read(bal);
    auth = bal - amount >= 0s{width:d};
  }} else {{
    throw;
  }}
}}

account.debit(s{width:d} amount) {{
  bool auth;
  if (P_db) {{
    account.canpay(amount, auth);
    if (auth) {{
      balance.write(amount);
    }} else {{ }}
  }} else {{
    throw;
  }}
}}

balance.read(s{width:d} &out) {{
  out = balance;
}}

balance.write(s{width:d} amount) {{
  balance = balance - amount;
}}
