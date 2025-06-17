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
  Stack::pop();

  modified = false;
  Stack::push(42);

  // modified = false;
  // T::Tcp();

  Stack::~Stack();
  T::~T();
}}

StackImpl::StackImpl(u{width:d} s) {{
  _::operator_new();
  vsize = s;
  vused = 0u{width:d};
}}

StackImpl::~StackImpl() {{
  std::destroy(0u{width:d}, vused);
  _::operator_delete();
}}

StackImpl::swap() {{
  std::swap();
  std::swap();
  std::swap();
}}

Stack::Stack() {{
  StackImpl::StackImpl(2);
}}

Stack::Stackcp() {{
  u{width:d} i, x;
  StackImpl::StackImpl(vsize);
  i = 0u{width:d};
  while (i < vused) {{
    std::construct(v[i], x);
    v[i] = x;
    i = i + 1u{width:d};
  }}
}}

Stack::operator=() {{
  Stack::Stackcp();
  StackImpl::swap();
}}

Stack::size() {{}}

Stack::push(u{width:d} t) {{
  u{width:d} i, oldvused;
  u{width:d}[6] oldv;
  if (vused == vsize) {{
    i = 0u{width:d};
    while (i < vused) {{
      oldv[i] = v[i];
      i = i + 1u{width:d};
    }}
    oldvused = vused;
    StackImpl::StackImpl(vsize + 2);
    while (vused < oldvused) {{
      Stack::push(oldv[vused]);
      vused = vused + 1u{width:d};
    }}
    Stack::push(t);
    StackImpl::swap();
  }} else {{
    std::construct(t, i);
    v[vused] = i;
    modified = true;
    vused = vused + 1u{width:d};
  }}
}}

Stack::top(u{width:d} &x) {{
  T::Tcp(v[vused], x);
}}

Stack::pop() {{
  if (vused == 0u{width:d}) {{
    throw;
  }} else {{
    std::destroy(vused - 1u{width:d}, vused);
    vused = vused - 1u{width:d};
    modified = true;
  }}
}}

Stack::~Stack() {{
  StackImpl::~StackImpl();
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

T::operator=(u{width:d} src, u{width:d} &dst) {{
  if (*) {{
    throw;
  }} else {{
    dst = src;
  }}
}}

T::~T() {{}}

std::swap() {{
  modified = true;
}}

std::construct(u{width:d} src, u{width:d} &dst) {{
  T::Tcp(src, dst);
}}

std::destroy(u{width:d} from, u{width:d} to) {{
  while (from < to) {{
    T::~T();
    from = from + 1u{width:d};
  }}
}}

_::operator_new() {{
  if (*) {{
    throw;
  }} else {{}}
}}
_::operator_delete() {{}}
