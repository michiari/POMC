/* Taken from:
 *   T. Jensen, D. Le Metayer and T. Thorn,
 *   "Verification of control flow based security properties",
 *   Proceedings of the 1999 IEEE Symposium on Security and Privacy,
 *   Oakland, CA, USA, 1999, pp. 89-103, doi: 10.1109/SECPRI.1999.766902.
 */

public class ControlledVar {
    private float var;

    void write(float n) { // wr
        AccessController.checkPermission(Write);
        var = n;
    }

    float read() { // rd
        AccessController.checkPermission(Read);
        return var;
    }
}

public class AccountMan {
    private ControlledVar balance;

    public boolean canpay(float amount) { // cp
        AccessController.checkPermission(Canpay);
        boolean res = false;

        try {
            AccessController.beginPrivileged();
            res = balance.read() > amount;
        } finally {
            AccessController.endPrivileged();
        }

        return res;
    }

    public void debit(float amount) { // db
        AccessController.checkPermission(Debit);
        if (this.canpay(amount)) {
            try {
                AccessController.beginPrivileged();
                balance.write(balance.read() - amount);
            } finally {
                AccessController.endPrivileged();
            }
        } else {
            throw "can't pay!";
        }
    }
}

public void spender() { // sp
    float spend = 50;
    if (account.canpay(spend)) {
        account.debit(spend);
    }
    if (*) {
        spender();
    }
}

public void clyde() { // cl
    account.debit(50000000);
    if (*) {
        clyde();
    }
}
