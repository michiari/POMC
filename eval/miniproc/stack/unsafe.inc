bool modified;
u{width:d} vsize, vused;
u{width:d}[4] v;

main() {{
  u{width:d} a;
  modified = false;

  Stack::Stack();

  a = {aval};
  Stack::push(a);

  modified = false;
  Stack::pop(a);

  modified = false;
  Stack::push(42);

  modified = false;
  // T::Tcp();

  Stack::~Stack();
  T::~T();
}}

Stack::Stack() {{
  vsize = 2;
  vused = 0;
  T::operator_new(vsize);
}}

Stack::~Stack() {{
  T::operator_delete();
}}

Stack::Stackcp() {{
  Stack::NewCopy(vsize, vsize);
}}

Stack::operator=() {{
  if (*) {{
    Stack::NewCopy(vsize, vsize);
    T::operator_delete();
  }} else {{}}
}}

Stack::push(u{width:d} t) {{
  u{width:d} x;
  if (vused == vsize) {{
    Stack::NewCopy(vsize, vsize + 2);
    T::operator_delete();
    vsize = vsize + 2;
  }} else {{}}
  T::operator=(t, x);
  v[vused] = x; // TODO: allow array access in ref parameter
  modified = true;
  vused = vused + 1;
}}

Stack::pop(u{width:d} &topv) {{
  if (vused == 0u{width:d}) {{
    throw;
  }} else {{
    vused = vused - 1;
    modified = true;
    T::Tcp(v[vused], topv);
  }}
}}

Stack::NewCopy(u{width:d} srcsize, u{width:d} dstsize) {{
  T::operator_new(dstsize);
  try {{
    std::copy(srcsize);
  }} catch {{
    T::operator_delete();
    throw;
  }}
}}

T::T(u{width:d} &val) {{
  if (*) {{
    throw;
  }} else {{
    val = 0u{width:d};
  }}
}}

T::Tcp(u{width:d} src, u{width:d} &dst) {{
  T::operator=(src, dst);
}}

T::operator_new(u{width:d} size) {{
  u{width:d} i, x;
  if (*) {{
    throw;
  }} else {{
    i = 0u{width:d};
    while (i < size) {{
      T::T(x);
      v[i] = x; // TODO: allow array access in ref parameter
      i = i + 1u{width:d};
    }}
  }}
}}

T::operator=(u{width:d} src, u{width:d} &dst) {{
  if (*) {{
    throw;
  }} else {{
    dst = src;
  }}
}}

T::operator_delete() {{}}
T::~T() {{}}

std::copy(u{width:d} end) {{
  u{width:d} i, x;
  i = 0u{width:d};
  while (i < end) {{
    T::operator=(v[i], x);
    v[i] = x; // TODO: allow array access in ref parameter
    i = i + 1u{width:d};
  }}
}}
