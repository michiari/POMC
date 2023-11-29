bool sorted;
u{width:d}[{size:d}] a;

main() {{
        {init}

        try {{
                qs(0s6, {size:d}s6 - 1s6);
        }} catch {{

        }}
}}

qs(s6 left, s6 right) {{
        s6 lo, hi, eq;
        u{width:d} piv;

        if (left >= right) {{
        }} else {{
                piv = a[right];
                eq = left;
                lo = eq;
                hi = right;
                while (lo <= hi) {{
                        if (a[hi] > piv){{
                                hi = hi - 1s6;
                        }} else {{
                                swapElements(lo, hi);
                                if (a[lo] < piv){{
                                        swapElements(lo, eq);
                                        eq = eq + 1s6;
                                }} else {{}}
                                lo = lo + 1s6;
                        }}
                }}
                qs(left,eq-1s6);
                qs(lo,right);
        }}
}}

swapElements(s6 swapLeft, s6 swapRight) {{
    u{width:d} tmp;

    accessValues();
        tmp = a[swapLeft];
        a[swapLeft] = a[swapRight];
        a[swapRight] = tmp;
        sorted = {comp};
}}

accessValues(){{
        if (*){{
                throw;
        }} else {{}}
}}
