package Console;

import Chess.ChessBoard;
import Chess.Tile;

public class BoardDisplay {
    /*@
    @ requires board != null && board.getBoardArray() != null;
    @ requires board.getBoardArray().length == 8;
    @ requires (\forall int i; 0 <= i && i < board.getBoardArray().length;
    @              board.getBoardArray()[i] != null &&
    @              board.getBoardArray()[i].length == 8 &&
    @              (\forall int j; 0 <= j && j < board.getBoardArray()[i].length;
    @                  board.getBoardArray()[i][j] != null));
    @ ensures true;
    @*/
    public static void printBoard(ChessBoard board) {
        clearConsole();
        Tile[][] b = board.getBoardArray();

        //@ assert b != null && b.length == 8;
        //@ assert (\forall int i; 0 <= i && i < b.length;
        //@            b[i] != null && b[i].length == 8 &&
        //@            (\forall int j; 0 <= j && j < b[i].length; b[i][j] != null));

        System.out.println();
        System.out.println("      [A][B][C][D][E][F][G][H] \n");

        //@ maintaining 0 <= i && i <= 8;
        //@ decreases 8 - i;
        for (int i = 0; i < 8; i++) {
            //@ assert b[i] != null && b[i].length == 8;
            System.out.print("[" + (8 - i) + "]   ");

            //@ maintaining 0 <= j && j <= 8;
            //@ decreases 8 - j;
            for (int j = 0; j < 8; j++) {
                //@ assert b[i][j] != null;
                System.out.print(b[i][j].getValue());
            }

            System.out.println("   [" + (8 - i) + "]");
        }

        System.out.println("\n      [A][B][C][D][E][F][G][H]\n");
    }

    /*@ public normal_behavior
    @ ensures true;
    @ assignable \everything;
    @*/
    public static void clearConsole() {
        /*@ nullable @*/ String errorMessage = null;
        try {
            final String os = System.getProperty("os.name");

            if (os.contains("Windows")) {
                System.out.print("\033[H\033[2J");
            } else {
                //@ assume Runtime.getRuntime() != null;
                Runtime.getRuntime().exec("clear");
            }
        } catch (final Exception e) {
            //@ assume System.out != null && System.out.eol != null && System.out.eol.length() > 0;
            errorMessage = "Error while trying to clear console";
        }

        if (errorMessage != null && System.err != null) {
            //@ assume System.out != null && System.out.outputText != null && \invariant_for(System.out.outputText);
            System.out.println(errorMessage);
        }
    }
}
