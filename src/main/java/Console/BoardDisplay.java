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

        //@ assume b != null && b.length == 8;

        printLine("");
        printLine("      [A][B][C][D][E][F][G][H] \n");

        //@ maintaining 0 <= i && i <= 8;
        //@ decreases 8 - i;
        //@ maintaining (\forall int k; 0 <= k && k < i; b[k] != null && b[k].length == 8);
        for (int i = 0; i < 8; i++) {
            //@ assume b[i] != null && b[i].length == 8;
            printText("[" + (8 - i) + "]   ");

            //@ maintaining 0 <= j && j <= 8;
            //@ decreases 8 - j;
            //@ maintaining (\forall int k; 0 <= k && k < j; b[i][k] != null);
            for (int j = 0; j < 8; j++) {
                //@ assume b[i][j] != null;
                printText(safeGetValue(b[i][j]));
            }

            printLine("   [" + (8 - i) + "]");
        }

        printLine("\n      [A][B][C][D][E][F][G][H]\n");
    }

    /*@ requires tile != null;
    @ ensures \result != null;
    @*/
    private static String safeGetValue(Tile tile) {
        String value = tile.getValue();
        return value;
    }


    /*@ assignable System.out.outputText, System.out.eol;
      @ ensures true;
      @ signals (Exception e) false; 
      @*/
    private static void printLine(String line) {
        if (System.out != null) {
            System.out.println(line);
        }
    }

    /*@ requires text != null;
      @ ensures true;
      @ assignable System.out.outputText, System.out.eol;
      @ signals (Exception e) false; 
      @*/
    private static void printText(String text) {
        if (System.out != null) {
            System.out.print(text);
        }
    }

    /*@ ensures true;
      @ assignable \everything;
      @*/
    public static void clearConsole() {
        try {
            final String os = System.getProperty("os.name");

            if (os.contains("Windows")) {
                System.out.print("\033[H\033[2J");
            } 
        } catch (final Exception e) {
            printErro();
        }
    }

    //@ assignable System.out.outputText, System.out.eol;
    private static void printErro() {
        System.out.println("Error while trying to clear console");
    }
}
