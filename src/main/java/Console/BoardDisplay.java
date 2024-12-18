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
    public static void printBoard(ChessBoard board){
        clearConsole();
        Tile[][] b = board.getBoardArray();

        System.out.println();
        System.out.println("      [A][B][C][D][E][F][G][H] \n");

        //@ maintaining 0 <= i && i <= 8;
        //@ maintaining (\forall int k; 0 <= k && k < i;
        //@                (\forall int j; 0 <= j && j < 8; b[k][j] != null));
        // loop_writes i, System.out.outputText, System.out.eol;
        //@ decreases 8 - i;
        for(int i = 0; i < 8; i++) {
            System.out.print("[" + (8 - i) + "]   ");

            //@ maintaining 0 <= j && j <= 8;
            //@ maintaining (\forall int k; 0 <= k && k < j; b[i][k] != null);
            //@ maintaining b[i] != null && b[i].length == 8;
            // loop_writes j, System.out.outputText;
            //@ decreases 8 - j;
            for (int j = 0; j < 8; j++){
                //@ assert 0 <= i && i < 8;
                //@ assert 0 <= j && j < 8;
                //@ assert b[i] != null && b[i][j] != null; 
                System.out.print(b[i][j].getValue());
            }

            System.out.println("   [" + (8 - i) + "]");
        }

        System.out.println("\n      [A][B][C][D][E][F][G][H]\n");
    }

    /*@ public normal_behavior
      @ ensures true;
      @*/
    public static void clearConsole() {
        try {
            final String os = System.getProperty("os.name");

            if (os.contains("Windows")) {
                System.out.print("\033[H\033[2J");
            } else {
                Runtime.getRuntime().exec("clear");
            }
        } catch (final Exception e) {
            System.err.println("Error while trying to clear console");
        }
    }
}
